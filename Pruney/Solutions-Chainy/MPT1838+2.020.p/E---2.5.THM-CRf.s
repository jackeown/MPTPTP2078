%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:18:41 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 125 expanded)
%              Number of clauses        :   43 (  55 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  186 ( 446 expanded)
%              Number of equality atoms :   55 (  95 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t1_tex_2,conjecture,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(d3_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            | r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(t44_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ~ ( k1_tarski(X1) = k2_xboole_0(X2,X3)
        & X2 != X3
        & X2 != k1_xboole_0
        & X3 != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t7_ordinal1,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_zfmisc_1(X2) )
           => ( r1_tarski(X1,X2)
             => X1 = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t1_tex_2])).

fof(c_0_12,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X18,X17)
        | r2_hidden(X18,X15)
        | r2_hidden(X18,X16)
        | X17 != k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X15)
        | r2_hidden(X19,X17)
        | X17 != k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X19,X16)
        | r2_hidden(X19,X17)
        | X17 != k2_xboole_0(X15,X16) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X20)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_xboole_0(X20,X21) )
      & ( ~ r2_hidden(esk3_3(X20,X21,X22),X21)
        | ~ r2_hidden(esk3_3(X20,X21,X22),X22)
        | X22 = k2_xboole_0(X20,X21) )
      & ( r2_hidden(esk3_3(X20,X21,X22),X22)
        | r2_hidden(esk3_3(X20,X21,X22),X20)
        | r2_hidden(esk3_3(X20,X21,X22),X21)
        | X22 = k2_xboole_0(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).

fof(c_0_13,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0)
    & ~ v1_xboole_0(esk6_0)
    & v1_zfmisc_1(esk6_0)
    & r1_tarski(esk5_0,esk6_0)
    & esk5_0 != esk6_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X3)
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_xboole_0(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( r2_hidden(X1,X2)
    | r2_hidden(X1,X3)
    | ~ r2_hidden(X1,k2_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X33)
      | ~ m1_subset_1(X34,X33)
      | k6_domain_1(X33,X34) = k1_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_21,plain,(
    ! [X27] : k2_tarski(X27,X27) = k1_tarski(X27) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_22,plain,(
    ! [X35,X37] :
      ( ( m1_subset_1(esk4_1(X35),X35)
        | ~ v1_zfmisc_1(X35)
        | v1_xboole_0(X35) )
      & ( X35 = k6_domain_1(X35,esk4_1(X35))
        | ~ v1_zfmisc_1(X35)
        | v1_xboole_0(X35) )
      & ( ~ m1_subset_1(X37,X35)
        | X35 != k6_domain_1(X35,X37)
        | v1_zfmisc_1(X35)
        | v1_xboole_0(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

cnf(c_0_23,negated_conjecture,
    ( r2_hidden(X1,esk6_0)
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(k2_xboole_0(X1,X2),X3)
    | r2_hidden(esk2_2(k2_xboole_0(X1,X2),X3),X2)
    | r2_hidden(esk2_2(k2_xboole_0(X1,X2),X3),X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2)
    | X3 != k2_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_26,plain,(
    ! [X28,X29,X30] :
      ( k1_tarski(X28) != k2_xboole_0(X29,X30)
      | X29 = X30
      | X29 = k1_xboole_0
      | X30 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_zfmisc_1])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( m1_subset_1(esk4_1(X1),X1)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( v1_zfmisc_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( ~ v1_xboole_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_32,plain,
    ( X1 = k6_domain_1(X1,esk4_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk5_0,X1),X2)
    | r2_hidden(esk2_2(k2_xboole_0(esk5_0,X1),X2),esk6_0)
    | r2_hidden(esk2_2(k2_xboole_0(esk5_0,X1),X2),X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( X2 = X3
    | X2 = k1_xboole_0
    | X3 = k1_xboole_0
    | k1_tarski(X1) != k2_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk4_1(esk6_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_38,negated_conjecture,
    ( k6_domain_1(esk6_0,esk4_1(esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_30]),c_0_31])).

fof(c_0_39,plain,(
    ! [X24,X25] :
      ( ( r1_tarski(X24,X25)
        | X24 != X25 )
      & ( r1_tarski(X25,X24)
        | X24 != X25 )
      & ( ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X25,X24)
        | X24 = X25 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk2_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk5_0,esk6_0),X1)
    | r2_hidden(esk2_2(k2_xboole_0(esk5_0,esk6_0),X1),esk6_0) ),
    inference(ef,[status(thm)],[c_0_33])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,X2)
    | r2_hidden(esk2_2(X1,X2),k2_xboole_0(X3,X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_19])).

fof(c_0_43,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_44,plain,
    ( X2 = X3
    | X3 = k1_xboole_0
    | X2 = k1_xboole_0
    | k2_tarski(X1,X1) != k2_xboole_0(X2,X3) ),
    inference(rw,[status(thm)],[c_0_35,c_0_28])).

cnf(c_0_45,negated_conjecture,
    ( k2_tarski(esk4_1(esk6_0),esk4_1(esk6_0)) = esk6_0 ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38]),c_0_31])).

cnf(c_0_46,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_xboole_0(esk5_0,esk6_0),esk6_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_48,plain,
    ( r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_42])).

cnf(c_0_49,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k1_xboole_0
    | X2 = k1_xboole_0
    | X1 = X2
    | k2_xboole_0(X1,X2) != esk6_0 ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( k2_xboole_0(esk5_0,esk6_0) = esk6_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_52,negated_conjecture,
    ( esk5_0 != esk6_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_53,plain,(
    ! [X31,X32] :
      ( ~ r2_hidden(X31,X32)
      | ~ r1_tarski(X32,X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).

cnf(c_0_54,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_19])).

cnf(c_0_55,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_56,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_58,negated_conjecture,
    ( esk6_0 = k1_xboole_0
    | esk5_0 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_59,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk1_1(esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_56]),c_0_57])).

cnf(c_0_62,negated_conjecture,
    ( esk6_0 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_55])])).

cnf(c_0_63,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_61,c_0_62]),c_0_63]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:24:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.19/0.41  # and selection function PSelectComplexPreferEQ.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t1_tex_2, conjecture, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 0.19/0.41  fof(d3_xboole_0, axiom, ![X1, X2, X3]:(X3=k2_xboole_0(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(r2_hidden(X4,X1)|r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 0.19/0.41  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.19/0.41  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.41  fof(d1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>(v1_zfmisc_1(X1)<=>?[X2]:(m1_subset_1(X2,X1)&X1=k6_domain_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 0.19/0.41  fof(t44_zfmisc_1, axiom, ![X1, X2, X3]:~((((k1_tarski(X1)=k2_xboole_0(X2,X3)&X2!=X3)&X2!=k1_xboole_0)&X3!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 0.19/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.41  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.41  fof(t7_ordinal1, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 0.19/0.41  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.41  fof(c_0_11, negated_conjecture, ~(![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2)))), inference(assume_negation,[status(cth)],[t1_tex_2])).
% 0.19/0.41  fof(c_0_12, plain, ![X15, X16, X17, X18, X19, X20, X21, X22]:(((~r2_hidden(X18,X17)|(r2_hidden(X18,X15)|r2_hidden(X18,X16))|X17!=k2_xboole_0(X15,X16))&((~r2_hidden(X19,X15)|r2_hidden(X19,X17)|X17!=k2_xboole_0(X15,X16))&(~r2_hidden(X19,X16)|r2_hidden(X19,X17)|X17!=k2_xboole_0(X15,X16))))&(((~r2_hidden(esk3_3(X20,X21,X22),X20)|~r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k2_xboole_0(X20,X21))&(~r2_hidden(esk3_3(X20,X21,X22),X21)|~r2_hidden(esk3_3(X20,X21,X22),X22)|X22=k2_xboole_0(X20,X21)))&(r2_hidden(esk3_3(X20,X21,X22),X22)|(r2_hidden(esk3_3(X20,X21,X22),X20)|r2_hidden(esk3_3(X20,X21,X22),X21))|X22=k2_xboole_0(X20,X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_xboole_0])])])])])])).
% 0.19/0.41  fof(c_0_13, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.19/0.41  fof(c_0_14, negated_conjecture, (~v1_xboole_0(esk5_0)&((~v1_xboole_0(esk6_0)&v1_zfmisc_1(esk6_0))&(r1_tarski(esk5_0,esk6_0)&esk5_0!=esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.19/0.41  cnf(c_0_15, plain, (r2_hidden(X1,X3)|r2_hidden(X1,X4)|~r2_hidden(X1,X2)|X2!=k2_xboole_0(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_16, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_17, negated_conjecture, (r1_tarski(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_18, plain, (r2_hidden(X1,X2)|r2_hidden(X1,X3)|~r2_hidden(X1,k2_xboole_0(X3,X2))), inference(er,[status(thm)],[c_0_15])).
% 0.19/0.41  cnf(c_0_19, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  fof(c_0_20, plain, ![X33, X34]:(v1_xboole_0(X33)|~m1_subset_1(X34,X33)|k6_domain_1(X33,X34)=k1_tarski(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.41  fof(c_0_21, plain, ![X27]:k2_tarski(X27,X27)=k1_tarski(X27), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  fof(c_0_22, plain, ![X35, X37]:(((m1_subset_1(esk4_1(X35),X35)|~v1_zfmisc_1(X35)|v1_xboole_0(X35))&(X35=k6_domain_1(X35,esk4_1(X35))|~v1_zfmisc_1(X35)|v1_xboole_0(X35)))&(~m1_subset_1(X37,X35)|X35!=k6_domain_1(X35,X37)|v1_zfmisc_1(X35)|v1_xboole_0(X35))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (r2_hidden(X1,esk6_0)|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.19/0.41  cnf(c_0_24, plain, (r1_tarski(k2_xboole_0(X1,X2),X3)|r2_hidden(esk2_2(k2_xboole_0(X1,X2),X3),X2)|r2_hidden(esk2_2(k2_xboole_0(X1,X2),X3),X1)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.19/0.41  cnf(c_0_25, plain, (r2_hidden(X1,X3)|~r2_hidden(X1,X2)|X3!=k2_xboole_0(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  fof(c_0_26, plain, ![X28, X29, X30]:(k1_tarski(X28)!=k2_xboole_0(X29,X30)|X29=X30|X29=k1_xboole_0|X30=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_zfmisc_1])])).
% 0.19/0.41  cnf(c_0_27, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.41  cnf(c_0_28, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_29, plain, (m1_subset_1(esk4_1(X1),X1)|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (v1_zfmisc_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (~v1_xboole_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_32, plain, (X1=k6_domain_1(X1,esk4_1(X1))|v1_xboole_0(X1)|~v1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (r1_tarski(k2_xboole_0(esk5_0,X1),X2)|r2_hidden(esk2_2(k2_xboole_0(esk5_0,X1),X2),esk6_0)|r2_hidden(esk2_2(k2_xboole_0(esk5_0,X1),X2),X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.41  cnf(c_0_34, plain, (r2_hidden(X1,k2_xboole_0(X2,X3))|~r2_hidden(X1,X3)), inference(er,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_35, plain, (X2=X3|X2=k1_xboole_0|X3=k1_xboole_0|k1_tarski(X1)!=k2_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_36, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.41  cnf(c_0_37, negated_conjecture, (m1_subset_1(esk4_1(esk6_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (k6_domain_1(esk6_0,esk4_1(esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_30]), c_0_31])).
% 0.19/0.41  fof(c_0_39, plain, ![X24, X25]:(((r1_tarski(X24,X25)|X24!=X25)&(r1_tarski(X25,X24)|X24!=X25))&(~r1_tarski(X24,X25)|~r1_tarski(X25,X24)|X24=X25)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.41  cnf(c_0_40, plain, (r1_tarski(X1,X2)|~r2_hidden(esk2_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_41, negated_conjecture, (r1_tarski(k2_xboole_0(esk5_0,esk6_0),X1)|r2_hidden(esk2_2(k2_xboole_0(esk5_0,esk6_0),X1),esk6_0)), inference(ef,[status(thm)],[c_0_33])).
% 0.19/0.41  cnf(c_0_42, plain, (r1_tarski(X1,X2)|r2_hidden(esk2_2(X1,X2),k2_xboole_0(X3,X1))), inference(spm,[status(thm)],[c_0_34, c_0_19])).
% 0.19/0.41  fof(c_0_43, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.41  cnf(c_0_44, plain, (X2=X3|X3=k1_xboole_0|X2=k1_xboole_0|k2_tarski(X1,X1)!=k2_xboole_0(X2,X3)), inference(rw,[status(thm)],[c_0_35, c_0_28])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (k2_tarski(esk4_1(esk6_0),esk4_1(esk6_0))=esk6_0), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38]), c_0_31])).
% 0.19/0.41  cnf(c_0_46, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.41  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_xboole_0(esk5_0,esk6_0),esk6_0)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.41  cnf(c_0_48, plain, (r1_tarski(X1,k2_xboole_0(X2,X1))), inference(spm,[status(thm)],[c_0_40, c_0_42])).
% 0.19/0.41  cnf(c_0_49, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (X1=k1_xboole_0|X2=k1_xboole_0|X1=X2|k2_xboole_0(X1,X2)!=esk6_0), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (k2_xboole_0(esk5_0,esk6_0)=esk6_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (esk5_0!=esk6_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  fof(c_0_53, plain, ![X31, X32]:(~r2_hidden(X31,X32)|~r1_tarski(X32,X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_ordinal1])])).
% 0.19/0.41  cnf(c_0_54, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_49, c_0_19])).
% 0.19/0.41  cnf(c_0_55, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.41  cnf(c_0_56, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (esk6_0=k1_xboole_0|esk5_0=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_52])).
% 0.19/0.41  cnf(c_0_59, plain, (~r2_hidden(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.19/0.41  cnf(c_0_60, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (r2_hidden(esk1_1(esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_56]), c_0_57])).
% 0.19/0.41  cnf(c_0_62, negated_conjecture, (esk6_0=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_55])])).
% 0.19/0.41  cnf(c_0_63, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.19/0.41  cnf(c_0_64, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_61, c_0_62]), c_0_63]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 65
% 0.19/0.41  # Proof object clause steps            : 43
% 0.19/0.41  # Proof object formula steps           : 22
% 0.19/0.41  # Proof object conjectures             : 21
% 0.19/0.41  # Proof object clause conjectures      : 18
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 20
% 0.19/0.41  # Proof object initial formulas used   : 11
% 0.19/0.41  # Proof object generating inferences   : 18
% 0.19/0.41  # Proof object simplifying inferences  : 16
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 12
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 28
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 27
% 0.19/0.41  # Processed clauses                    : 958
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 647
% 0.19/0.41  # ...remaining for further processing  : 311
% 0.19/0.41  # Other redundant clauses eliminated   : 5
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 1
% 0.19/0.41  # Backward-rewritten                   : 146
% 0.19/0.41  # Generated clauses                    : 2539
% 0.19/0.41  # ...of the previous two non-trivial   : 2218
% 0.19/0.41  # Contextual simplify-reflections      : 1
% 0.19/0.41  # Paramodulations                      : 2326
% 0.19/0.41  # Factorizations                       : 208
% 0.19/0.41  # Equation resolutions                 : 5
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 133
% 0.19/0.41  #    Positive orientable unit clauses  : 13
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 9
% 0.19/0.41  #    Non-unit-clauses                  : 111
% 0.19/0.41  # Current number of unprocessed clauses: 1212
% 0.19/0.41  # ...number of literals in the above   : 4071
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 174
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 3827
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 2868
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 410
% 0.19/0.41  # Unit Clause-clause subsumption calls : 259
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 160
% 0.19/0.41  # BW rewrite match successes           : 6
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 30444
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.074 s
% 0.19/0.41  # System time              : 0.005 s
% 0.19/0.41  # Total time               : 0.080 s
% 0.19/0.41  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
