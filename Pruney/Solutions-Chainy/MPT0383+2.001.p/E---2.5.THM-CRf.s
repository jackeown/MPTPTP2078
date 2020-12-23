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
% DateTime   : Thu Dec  3 10:46:59 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   31 (  48 expanded)
%              Number of clauses        :   20 (  23 expanded)
%              Number of leaves         :    5 (  11 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 254 expanded)
%              Number of equality atoms :   23 (  57 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t65_subset_1,conjecture,(
    ! [X1,X2,X3,X4] :
      ~ ( r2_hidden(X4,X3)
        & r1_tarski(X3,k2_zfmisc_1(X1,X2))
        & ! [X5] :
            ( m1_subset_1(X5,X1)
           => ! [X6] :
                ( m1_subset_1(X6,X2)
               => X4 != k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_subset_1)).

fof(d2_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_zfmisc_1(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5,X6] :
              ( r2_hidden(X5,X1)
              & r2_hidden(X6,X2)
              & X4 = k4_tarski(X5,X6) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1,X2,X3,X4] :
        ~ ( r2_hidden(X4,X3)
          & r1_tarski(X3,k2_zfmisc_1(X1,X2))
          & ! [X5] :
              ( m1_subset_1(X5,X1)
             => ! [X6] :
                  ( m1_subset_1(X6,X2)
                 => X4 != k4_tarski(X5,X6) ) ) ) ),
    inference(assume_negation,[status(cth)],[t65_subset_1])).

fof(c_0_6,plain,(
    ! [X17,X18,X19,X20,X23,X24,X25,X26,X27,X28,X30,X31] :
      ( ( r2_hidden(esk3_4(X17,X18,X19,X20),X17)
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( r2_hidden(esk4_4(X17,X18,X19,X20),X18)
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( X20 = k4_tarski(esk3_4(X17,X18,X19,X20),esk4_4(X17,X18,X19,X20))
        | ~ r2_hidden(X20,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( ~ r2_hidden(X24,X17)
        | ~ r2_hidden(X25,X18)
        | X23 != k4_tarski(X24,X25)
        | r2_hidden(X23,X19)
        | X19 != k2_zfmisc_1(X17,X18) )
      & ( ~ r2_hidden(esk5_3(X26,X27,X28),X28)
        | ~ r2_hidden(X30,X26)
        | ~ r2_hidden(X31,X27)
        | esk5_3(X26,X27,X28) != k4_tarski(X30,X31)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( r2_hidden(esk6_3(X26,X27,X28),X26)
        | r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( r2_hidden(esk7_3(X26,X27,X28),X27)
        | r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) )
      & ( esk5_3(X26,X27,X28) = k4_tarski(esk6_3(X26,X27,X28),esk7_3(X26,X27,X28))
        | r2_hidden(esk5_3(X26,X27,X28),X28)
        | X28 = k2_zfmisc_1(X26,X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).

fof(c_0_7,negated_conjecture,(
    ! [X40,X41] :
      ( r2_hidden(esk11_0,esk10_0)
      & r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,esk9_0))
      & ( ~ m1_subset_1(X40,esk8_0)
        | ~ m1_subset_1(X41,esk9_0)
        | esk11_0 != k4_tarski(X40,X41) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( X1 = k4_tarski(esk3_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))
    | ~ r2_hidden(X1,X4)
    | X4 != k2_zfmisc_1(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_9,plain,(
    ! [X34,X35] :
      ( ( ~ m1_subset_1(X35,X34)
        | r2_hidden(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ r2_hidden(X35,X34)
        | m1_subset_1(X35,X34)
        | v1_xboole_0(X34) )
      & ( ~ m1_subset_1(X35,X34)
        | v1_xboole_0(X35)
        | ~ v1_xboole_0(X34) )
      & ( ~ v1_xboole_0(X35)
        | m1_subset_1(X35,X34)
        | ~ v1_xboole_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_10,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_11,negated_conjecture,
    ( ~ m1_subset_1(X1,esk8_0)
    | ~ m1_subset_1(X2,esk9_0)
    | esk11_0 != k4_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k4_tarski(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3)) = X3
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,X2)
    | v1_xboole_0(X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ m1_subset_1(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk9_0)
    | ~ m1_subset_1(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk8_0)
    | ~ r2_hidden(esk11_0,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12])])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(csr,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( ~ m1_subset_1(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk8_0)
    | ~ r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk9_0)
    | ~ r2_hidden(esk11_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_18,plain,
    ( r2_hidden(esk4_4(X1,X2,X3,X4),X2)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( ~ r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk9_0)
    | ~ r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk8_0)
    | ~ r2_hidden(esk11_0,k2_zfmisc_1(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_18])).

cnf(c_0_21,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X1)
    | ~ r2_hidden(X4,X3)
    | X3 != k2_zfmisc_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_22,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r2_hidden(esk3_4(X1,esk9_0,k2_zfmisc_1(X1,esk9_0),esk11_0),esk8_0)
    | ~ r2_hidden(esk11_0,k2_zfmisc_1(X1,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)
    | ~ r2_hidden(X3,k2_zfmisc_1(X1,X2)) ),
    inference(er,[status(thm)],[c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_27,negated_conjecture,
    ( ~ r2_hidden(esk11_0,k2_zfmisc_1(esk8_0,esk9_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(esk8_0,esk9_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk11_0,esk10_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:11:40 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.18/0.43  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SOS_SP_PS_S5PRR_RG_S04AN
% 0.18/0.43  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.18/0.43  #
% 0.18/0.43  # Preprocessing time       : 0.027 s
% 0.18/0.43  # Presaturation interreduction done
% 0.18/0.43  
% 0.18/0.43  # Proof found!
% 0.18/0.43  # SZS status Theorem
% 0.18/0.43  # SZS output start CNFRefutation
% 0.18/0.43  fof(t65_subset_1, conjecture, ![X1, X2, X3, X4]:~(((r2_hidden(X4,X3)&r1_tarski(X3,k2_zfmisc_1(X1,X2)))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>X4!=k4_tarski(X5,X6))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_subset_1)).
% 0.18/0.43  fof(d2_zfmisc_1, axiom, ![X1, X2, X3]:(X3=k2_zfmisc_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5, X6]:((r2_hidden(X5,X1)&r2_hidden(X6,X2))&X4=k4_tarski(X5,X6)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 0.18/0.43  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.18/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.18/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.18/0.43  fof(c_0_5, negated_conjecture, ~(![X1, X2, X3, X4]:~(((r2_hidden(X4,X3)&r1_tarski(X3,k2_zfmisc_1(X1,X2)))&![X5]:(m1_subset_1(X5,X1)=>![X6]:(m1_subset_1(X6,X2)=>X4!=k4_tarski(X5,X6)))))), inference(assume_negation,[status(cth)],[t65_subset_1])).
% 0.18/0.43  fof(c_0_6, plain, ![X17, X18, X19, X20, X23, X24, X25, X26, X27, X28, X30, X31]:(((((r2_hidden(esk3_4(X17,X18,X19,X20),X17)|~r2_hidden(X20,X19)|X19!=k2_zfmisc_1(X17,X18))&(r2_hidden(esk4_4(X17,X18,X19,X20),X18)|~r2_hidden(X20,X19)|X19!=k2_zfmisc_1(X17,X18)))&(X20=k4_tarski(esk3_4(X17,X18,X19,X20),esk4_4(X17,X18,X19,X20))|~r2_hidden(X20,X19)|X19!=k2_zfmisc_1(X17,X18)))&(~r2_hidden(X24,X17)|~r2_hidden(X25,X18)|X23!=k4_tarski(X24,X25)|r2_hidden(X23,X19)|X19!=k2_zfmisc_1(X17,X18)))&((~r2_hidden(esk5_3(X26,X27,X28),X28)|(~r2_hidden(X30,X26)|~r2_hidden(X31,X27)|esk5_3(X26,X27,X28)!=k4_tarski(X30,X31))|X28=k2_zfmisc_1(X26,X27))&(((r2_hidden(esk6_3(X26,X27,X28),X26)|r2_hidden(esk5_3(X26,X27,X28),X28)|X28=k2_zfmisc_1(X26,X27))&(r2_hidden(esk7_3(X26,X27,X28),X27)|r2_hidden(esk5_3(X26,X27,X28),X28)|X28=k2_zfmisc_1(X26,X27)))&(esk5_3(X26,X27,X28)=k4_tarski(esk6_3(X26,X27,X28),esk7_3(X26,X27,X28))|r2_hidden(esk5_3(X26,X27,X28),X28)|X28=k2_zfmisc_1(X26,X27))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_zfmisc_1])])])])])])).
% 0.18/0.43  fof(c_0_7, negated_conjecture, ![X40, X41]:((r2_hidden(esk11_0,esk10_0)&r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,esk9_0)))&(~m1_subset_1(X40,esk8_0)|(~m1_subset_1(X41,esk9_0)|esk11_0!=k4_tarski(X40,X41)))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.18/0.43  cnf(c_0_8, plain, (X1=k4_tarski(esk3_4(X2,X3,X4,X1),esk4_4(X2,X3,X4,X1))|~r2_hidden(X1,X4)|X4!=k2_zfmisc_1(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.43  fof(c_0_9, plain, ![X34, X35]:(((~m1_subset_1(X35,X34)|r2_hidden(X35,X34)|v1_xboole_0(X34))&(~r2_hidden(X35,X34)|m1_subset_1(X35,X34)|v1_xboole_0(X34)))&((~m1_subset_1(X35,X34)|v1_xboole_0(X35)|~v1_xboole_0(X34))&(~v1_xboole_0(X35)|m1_subset_1(X35,X34)|~v1_xboole_0(X34)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.18/0.43  fof(c_0_10, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.18/0.43  cnf(c_0_11, negated_conjecture, (~m1_subset_1(X1,esk8_0)|~m1_subset_1(X2,esk9_0)|esk11_0!=k4_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.43  cnf(c_0_12, plain, (k4_tarski(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3))=X3|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_8])).
% 0.18/0.43  cnf(c_0_13, plain, (m1_subset_1(X1,X2)|v1_xboole_0(X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.18/0.43  cnf(c_0_14, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.18/0.43  cnf(c_0_15, negated_conjecture, (~m1_subset_1(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk9_0)|~m1_subset_1(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk8_0)|~r2_hidden(esk11_0,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12])])).
% 0.18/0.43  cnf(c_0_16, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(csr,[status(thm)],[c_0_13, c_0_14])).
% 0.18/0.43  cnf(c_0_17, negated_conjecture, (~m1_subset_1(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk8_0)|~r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk9_0)|~r2_hidden(esk11_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.18/0.43  cnf(c_0_18, plain, (r2_hidden(esk4_4(X1,X2,X3,X4),X2)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.43  cnf(c_0_19, negated_conjecture, (~r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk9_0)|~r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),esk11_0),esk8_0)|~r2_hidden(esk11_0,k2_zfmisc_1(X1,X2))), inference(spm,[status(thm)],[c_0_17, c_0_16])).
% 0.18/0.43  cnf(c_0_20, plain, (r2_hidden(esk4_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X2)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_18])).
% 0.18/0.43  cnf(c_0_21, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X1)|~r2_hidden(X4,X3)|X3!=k2_zfmisc_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.18/0.43  fof(c_0_22, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.18/0.43  cnf(c_0_23, negated_conjecture, (~r2_hidden(esk3_4(X1,esk9_0,k2_zfmisc_1(X1,esk9_0),esk11_0),esk8_0)|~r2_hidden(esk11_0,k2_zfmisc_1(X1,esk9_0))), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.18/0.43  cnf(c_0_24, plain, (r2_hidden(esk3_4(X1,X2,k2_zfmisc_1(X1,X2),X3),X1)|~r2_hidden(X3,k2_zfmisc_1(X1,X2))), inference(er,[status(thm)],[c_0_21])).
% 0.18/0.43  cnf(c_0_25, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.18/0.43  cnf(c_0_26, negated_conjecture, (r1_tarski(esk10_0,k2_zfmisc_1(esk8_0,esk9_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.43  cnf(c_0_27, negated_conjecture, (~r2_hidden(esk11_0,k2_zfmisc_1(esk8_0,esk9_0))), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.18/0.43  cnf(c_0_28, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(esk8_0,esk9_0))|~r2_hidden(X1,esk10_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.18/0.43  cnf(c_0_29, negated_conjecture, (r2_hidden(esk11_0,esk10_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.18/0.43  cnf(c_0_30, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])]), ['proof']).
% 0.18/0.43  # SZS output end CNFRefutation
% 0.18/0.43  # Proof object total steps             : 31
% 0.18/0.43  # Proof object clause steps            : 20
% 0.18/0.43  # Proof object formula steps           : 11
% 0.18/0.43  # Proof object conjectures             : 13
% 0.18/0.43  # Proof object clause conjectures      : 10
% 0.18/0.43  # Proof object formula conjectures     : 3
% 0.18/0.43  # Proof object initial clauses used    : 9
% 0.18/0.43  # Proof object initial formulas used   : 5
% 0.18/0.43  # Proof object generating inferences   : 7
% 0.18/0.43  # Proof object simplifying inferences  : 7
% 0.18/0.43  # Training examples: 0 positive, 0 negative
% 0.18/0.43  # Parsed axioms                        : 5
% 0.18/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.18/0.43  # Initial clauses                      : 20
% 0.18/0.43  # Removed in clause preprocessing      : 0
% 0.18/0.43  # Initial clauses in saturation        : 20
% 0.18/0.43  # Processed clauses                    : 525
% 0.18/0.43  # ...of these trivial                  : 0
% 0.18/0.43  # ...subsumed                          : 216
% 0.18/0.43  # ...remaining for further processing  : 309
% 0.18/0.43  # Other redundant clauses eliminated   : 6
% 0.18/0.43  # Clauses deleted for lack of memory   : 0
% 0.18/0.43  # Backward-subsumed                    : 0
% 0.18/0.43  # Backward-rewritten                   : 0
% 0.18/0.43  # Generated clauses                    : 3034
% 0.18/0.43  # ...of the previous two non-trivial   : 3025
% 0.18/0.43  # Contextual simplify-reflections      : 1
% 0.18/0.43  # Paramodulations                      : 3029
% 0.18/0.43  # Factorizations                       : 0
% 0.18/0.43  # Equation resolutions                 : 6
% 0.18/0.43  # Propositional unsat checks           : 0
% 0.18/0.43  #    Propositional check models        : 0
% 0.18/0.43  #    Propositional check unsatisfiable : 0
% 0.18/0.43  #    Propositional clauses             : 0
% 0.18/0.43  #    Propositional clauses after purity: 0
% 0.18/0.43  #    Propositional unsat core size     : 0
% 0.18/0.43  #    Propositional preprocessing time  : 0.000
% 0.18/0.43  #    Propositional encoding time       : 0.000
% 0.18/0.43  #    Propositional solver time         : 0.000
% 0.18/0.43  #    Success case prop preproc time    : 0.000
% 0.18/0.43  #    Success case prop encoding time   : 0.000
% 0.18/0.43  #    Success case prop solver time     : 0.000
% 0.18/0.43  # Current number of processed clauses  : 285
% 0.18/0.43  #    Positive orientable unit clauses  : 3
% 0.18/0.43  #    Positive unorientable unit clauses: 0
% 0.18/0.43  #    Negative unit clauses             : 2
% 0.18/0.43  #    Non-unit-clauses                  : 280
% 0.18/0.43  # Current number of unprocessed clauses: 2540
% 0.18/0.43  # ...number of literals in the above   : 7391
% 0.18/0.43  # Current number of archived formulas  : 0
% 0.18/0.43  # Current number of archived clauses   : 20
% 0.18/0.43  # Clause-clause subsumption calls (NU) : 20623
% 0.18/0.43  # Rec. Clause-clause subsumption calls : 16375
% 0.18/0.43  # Non-unit clause-clause subsumptions  : 217
% 0.18/0.43  # Unit Clause-clause subsumption calls : 146
% 0.18/0.43  # Rewrite failures with RHS unbound    : 0
% 0.18/0.43  # BW rewrite match attempts            : 3
% 0.18/0.43  # BW rewrite match successes           : 0
% 0.18/0.43  # Condensation attempts                : 0
% 0.18/0.43  # Condensation successes               : 0
% 0.18/0.43  # Termbank termtop insertions          : 54723
% 0.18/0.43  
% 0.18/0.43  # -------------------------------------------------
% 0.18/0.43  # User time                : 0.092 s
% 0.18/0.43  # System time              : 0.002 s
% 0.18/0.43  # Total time               : 0.094 s
% 0.18/0.43  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
