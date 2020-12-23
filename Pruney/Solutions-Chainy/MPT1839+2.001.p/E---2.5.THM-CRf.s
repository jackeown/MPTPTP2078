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
% DateTime   : Thu Dec  3 11:18:46 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.08s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 172 expanded)
%              Number of clauses        :   32 (  83 expanded)
%              Number of leaves         :   11 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :  141 ( 496 expanded)
%              Number of equality atoms :   31 ( 122 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t17_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(t1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_zfmisc_1(X2) )
         => ( r1_tarski(X1,X2)
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(t2_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_zfmisc_1(X1) )
     => ! [X2] :
          ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
         => r1_tarski(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

fof(t29_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(t20_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3)
        & ! [X4] :
            ( ( r1_tarski(X4,X2)
              & r1_tarski(X4,X3) )
           => r1_tarski(X4,X1) ) )
     => X1 = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

fof(t31_xboole_1,axiom,(
    ! [X1,X2,X3] : r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(t30_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(X1,X2)
     => k2_xboole_0(X1,k3_xboole_0(X3,X2)) = k3_xboole_0(k2_xboole_0(X1,X3),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_xboole_1)).

fof(c_0_11,plain,(
    ! [X39,X40] :
      ( ~ r2_hidden(X39,X40)
      | ~ v1_xboole_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_12,plain,(
    ! [X9,X10,X11,X12,X13] :
      ( ( ~ r1_tarski(X9,X10)
        | ~ r2_hidden(X11,X9)
        | r2_hidden(X11,X10) )
      & ( r2_hidden(esk2_2(X12,X13),X12)
        | r1_tarski(X12,X13) )
      & ( ~ r2_hidden(esk2_2(X12,X13),X13)
        | r1_tarski(X12,X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_13,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_14,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_18,plain,(
    ! [X19,X20] : r1_tarski(k3_xboole_0(X19,X20),X19) ),
    inference(variable_rename,[status(thm)],[t17_xboole_1])).

fof(c_0_19,plain,(
    ! [X67,X68] :
      ( v1_xboole_0(X67)
      | v1_xboole_0(X68)
      | ~ v1_zfmisc_1(X68)
      | ~ r1_tarski(X67,X68)
      | X67 = X68 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_21,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_22,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v1_xboole_0(X1)
          & v1_zfmisc_1(X1) )
       => ! [X2] :
            ( ~ v1_xboole_0(k3_xboole_0(X1,X2))
           => r1_tarski(X1,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t2_tex_2])).

fof(c_0_23,plain,(
    ! [X30,X31,X32] : r1_tarski(k3_xboole_0(X30,X31),k2_xboole_0(X30,X32)) ),
    inference(variable_rename,[status(thm)],[t29_xboole_1])).

fof(c_0_24,plain,(
    ! [X28,X29] :
      ( ~ r1_tarski(X28,X29)
      | k3_xboole_0(X28,X29) = X28 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | X1 = X2
    | ~ v1_zfmisc_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_27,negated_conjecture,
    ( ~ v1_xboole_0(esk12_0)
    & v1_zfmisc_1(esk12_0)
    & ~ v1_xboole_0(k3_xboole_0(esk12_0,esk13_0))
    & ~ r1_tarski(esk12_0,esk13_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).

fof(c_0_28,plain,(
    ! [X24,X25,X26] :
      ( ( r1_tarski(esk5_3(X24,X25,X26),X25)
        | ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X24,X26)
        | X24 = k3_xboole_0(X25,X26) )
      & ( r1_tarski(esk5_3(X24,X25,X26),X26)
        | ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X24,X26)
        | X24 = k3_xboole_0(X25,X26) )
      & ( ~ r1_tarski(esk5_3(X24,X25,X26),X24)
        | ~ r1_tarski(X24,X25)
        | ~ r1_tarski(X24,X26)
        | X24 = k3_xboole_0(X25,X26) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).

cnf(c_0_29,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,plain,
    ( k3_xboole_0(X1,X2) = X1
    | v1_xboole_0(k3_xboole_0(X1,X2))
    | ~ v1_zfmisc_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_21]),c_0_26])).

cnf(c_0_33,negated_conjecture,
    ( v1_zfmisc_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r1_tarski(esk5_3(X1,X2,X3),X3)
    | X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_29])).

cnf(c_0_36,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2))
    | ~ r1_tarski(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

fof(c_0_37,plain,(
    ! [X36,X37,X38] : r1_tarski(k2_xboole_0(k3_xboole_0(X36,X37),k3_xboole_0(X36,X38)),k2_xboole_0(X37,X38)) ),
    inference(variable_rename,[status(thm)],[t31_xboole_1])).

fof(c_0_38,plain,(
    ! [X33,X34,X35] :
      ( ~ r1_tarski(X33,X34)
      | k2_xboole_0(X33,k3_xboole_0(X35,X34)) = k3_xboole_0(k2_xboole_0(X33,X35),X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_xboole_1])])).

cnf(c_0_39,negated_conjecture,
    ( ~ v1_xboole_0(k3_xboole_0(esk12_0,esk13_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( k3_xboole_0(esk12_0,X1) = esk12_0
    | v1_xboole_0(k3_xboole_0(esk12_0,X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = X2
    | r1_tarski(esk5_3(X2,X1,X2),X2)
    | ~ r1_tarski(X2,X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_42,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_35])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_44,plain,
    ( k2_xboole_0(X1,k3_xboole_0(X3,X2)) = k3_xboole_0(k2_xboole_0(X1,X3),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_45,negated_conjecture,
    ( k3_xboole_0(esk12_0,esk13_0) = esk12_0 ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( X1 = k3_xboole_0(X2,X3)
    | ~ r1_tarski(esk5_3(X1,X2,X3),X1)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_47,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = X1
    | r1_tarski(esk5_3(X1,k2_xboole_0(X1,X2),X1),X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,plain,
    ( r1_tarski(k3_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),X1),X3),k2_xboole_0(X2,X3))
    | ~ r1_tarski(k3_xboole_0(X1,X2),X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( k3_xboole_0(k2_xboole_0(X1,esk12_0),esk13_0) = k2_xboole_0(X1,esk12_0)
    | ~ r1_tarski(X1,esk13_0) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_50,plain,
    ( k3_xboole_0(k2_xboole_0(X1,X2),X1) = X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_35]),c_0_42])])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(k3_xboole_0(k2_xboole_0(esk12_0,esk12_0),X1),k2_xboole_0(esk13_0,X1))
    | ~ r1_tarski(esk12_0,X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( k2_xboole_0(esk13_0,esk12_0) = esk13_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_35])])).

cnf(c_0_53,negated_conjecture,
    ( ~ r1_tarski(esk12_0,esk13_0) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_50]),c_0_35])]),c_0_53]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:43:10 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  # Version: 2.5pre002
% 0.15/0.36  # No SInE strategy applied
% 0.15/0.36  # Trying AutoSched0 for 299 seconds
% 7.08/7.42  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 7.08/7.42  # and selection function PSelectComplexExceptUniqMaxHorn.
% 7.08/7.42  #
% 7.08/7.42  # Preprocessing time       : 0.029 s
% 7.08/7.42  
% 7.08/7.42  # Proof found!
% 7.08/7.42  # SZS status Theorem
% 7.08/7.42  # SZS output start CNFRefutation
% 7.08/7.42  fof(t7_boole, axiom, ![X1, X2]:~((r2_hidden(X1,X2)&v1_xboole_0(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_boole)).
% 7.08/7.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.08/7.42  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.08/7.42  fof(t17_xboole_1, axiom, ![X1, X2]:r1_tarski(k3_xboole_0(X1,X2),X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.08/7.42  fof(t1_tex_2, axiom, ![X1]:(~(v1_xboole_0(X1))=>![X2]:((~(v1_xboole_0(X2))&v1_zfmisc_1(X2))=>(r1_tarski(X1,X2)=>X1=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 7.08/7.42  fof(t2_tex_2, conjecture, ![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 7.08/7.42  fof(t29_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 7.08/7.42  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.08/7.42  fof(t20_xboole_1, axiom, ![X1, X2, X3]:(((r1_tarski(X1,X2)&r1_tarski(X1,X3))&![X4]:((r1_tarski(X4,X2)&r1_tarski(X4,X3))=>r1_tarski(X4,X1)))=>X1=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 7.08/7.42  fof(t31_xboole_1, axiom, ![X1, X2, X3]:r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_xboole_1)).
% 7.08/7.42  fof(t30_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(X1,X2)=>k2_xboole_0(X1,k3_xboole_0(X3,X2))=k3_xboole_0(k2_xboole_0(X1,X3),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_xboole_1)).
% 7.08/7.42  fof(c_0_11, plain, ![X39, X40]:(~r2_hidden(X39,X40)|~v1_xboole_0(X40)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).
% 7.08/7.42  fof(c_0_12, plain, ![X9, X10, X11, X12, X13]:((~r1_tarski(X9,X10)|(~r2_hidden(X11,X9)|r2_hidden(X11,X10)))&((r2_hidden(esk2_2(X12,X13),X12)|r1_tarski(X12,X13))&(~r2_hidden(esk2_2(X12,X13),X13)|r1_tarski(X12,X13)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 7.08/7.42  fof(c_0_13, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 7.08/7.42  cnf(c_0_14, plain, (~r2_hidden(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 7.08/7.42  cnf(c_0_15, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 7.08/7.42  cnf(c_0_16, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 7.08/7.42  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 7.08/7.42  fof(c_0_18, plain, ![X19, X20]:r1_tarski(k3_xboole_0(X19,X20),X19), inference(variable_rename,[status(thm)],[t17_xboole_1])).
% 7.08/7.42  fof(c_0_19, plain, ![X67, X68]:(v1_xboole_0(X67)|(v1_xboole_0(X68)|~v1_zfmisc_1(X68)|(~r1_tarski(X67,X68)|X67=X68))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_tex_2])])])])).
% 7.08/7.42  cnf(c_0_20, plain, (X1=X2|~r1_tarski(X1,X2)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 7.08/7.42  cnf(c_0_21, plain, (r1_tarski(k3_xboole_0(X1,X2),X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 7.08/7.42  fof(c_0_22, negated_conjecture, ~(![X1]:((~(v1_xboole_0(X1))&v1_zfmisc_1(X1))=>![X2]:(~(v1_xboole_0(k3_xboole_0(X1,X2)))=>r1_tarski(X1,X2)))), inference(assume_negation,[status(cth)],[t2_tex_2])).
% 7.08/7.42  fof(c_0_23, plain, ![X30, X31, X32]:r1_tarski(k3_xboole_0(X30,X31),k2_xboole_0(X30,X32)), inference(variable_rename,[status(thm)],[t29_xboole_1])).
% 7.08/7.42  fof(c_0_24, plain, ![X28, X29]:(~r1_tarski(X28,X29)|k3_xboole_0(X28,X29)=X28), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 7.08/7.42  cnf(c_0_25, plain, (v1_xboole_0(X1)|v1_xboole_0(X2)|X1=X2|~v1_zfmisc_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 7.08/7.42  cnf(c_0_26, plain, (k3_xboole_0(X1,X2)=X1|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 7.08/7.42  fof(c_0_27, negated_conjecture, ((~v1_xboole_0(esk12_0)&v1_zfmisc_1(esk12_0))&(~v1_xboole_0(k3_xboole_0(esk12_0,esk13_0))&~r1_tarski(esk12_0,esk13_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_22])])])])).
% 7.08/7.42  fof(c_0_28, plain, ![X24, X25, X26]:(((r1_tarski(esk5_3(X24,X25,X26),X25)|(~r1_tarski(X24,X25)|~r1_tarski(X24,X26))|X24=k3_xboole_0(X25,X26))&(r1_tarski(esk5_3(X24,X25,X26),X26)|(~r1_tarski(X24,X25)|~r1_tarski(X24,X26))|X24=k3_xboole_0(X25,X26)))&(~r1_tarski(esk5_3(X24,X25,X26),X24)|(~r1_tarski(X24,X25)|~r1_tarski(X24,X26))|X24=k3_xboole_0(X25,X26))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_xboole_1])])])])).
% 7.08/7.42  cnf(c_0_29, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 7.08/7.42  cnf(c_0_30, plain, (r1_tarski(k3_xboole_0(X1,X2),k2_xboole_0(X1,X3))), inference(split_conjunct,[status(thm)],[c_0_23])).
% 7.08/7.42  cnf(c_0_31, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 7.08/7.42  cnf(c_0_32, plain, (k3_xboole_0(X1,X2)=X1|v1_xboole_0(k3_xboole_0(X1,X2))|~v1_zfmisc_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_21]), c_0_26])).
% 7.08/7.42  cnf(c_0_33, negated_conjecture, (v1_zfmisc_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.08/7.42  cnf(c_0_34, plain, (r1_tarski(esk5_3(X1,X2,X3),X3)|X1=k3_xboole_0(X2,X3)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 7.08/7.42  cnf(c_0_35, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_29])).
% 7.08/7.42  cnf(c_0_36, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))|~r1_tarski(X1,X3)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 7.08/7.42  fof(c_0_37, plain, ![X36, X37, X38]:r1_tarski(k2_xboole_0(k3_xboole_0(X36,X37),k3_xboole_0(X36,X38)),k2_xboole_0(X37,X38)), inference(variable_rename,[status(thm)],[t31_xboole_1])).
% 7.08/7.42  fof(c_0_38, plain, ![X33, X34, X35]:(~r1_tarski(X33,X34)|k2_xboole_0(X33,k3_xboole_0(X35,X34))=k3_xboole_0(k2_xboole_0(X33,X35),X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_xboole_1])])).
% 7.08/7.42  cnf(c_0_39, negated_conjecture, (~v1_xboole_0(k3_xboole_0(esk12_0,esk13_0))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.08/7.42  cnf(c_0_40, negated_conjecture, (k3_xboole_0(esk12_0,X1)=esk12_0|v1_xboole_0(k3_xboole_0(esk12_0,X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 7.08/7.42  cnf(c_0_41, plain, (k3_xboole_0(X1,X2)=X2|r1_tarski(esk5_3(X2,X1,X2),X2)|~r1_tarski(X2,X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 7.08/7.42  cnf(c_0_42, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_36, c_0_35])).
% 7.08/7.42  cnf(c_0_43, plain, (r1_tarski(k2_xboole_0(k3_xboole_0(X1,X2),k3_xboole_0(X1,X3)),k2_xboole_0(X2,X3))), inference(split_conjunct,[status(thm)],[c_0_37])).
% 7.08/7.42  cnf(c_0_44, plain, (k2_xboole_0(X1,k3_xboole_0(X3,X2))=k3_xboole_0(k2_xboole_0(X1,X3),X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 7.08/7.42  cnf(c_0_45, negated_conjecture, (k3_xboole_0(esk12_0,esk13_0)=esk12_0), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 7.08/7.42  cnf(c_0_46, plain, (X1=k3_xboole_0(X2,X3)|~r1_tarski(esk5_3(X1,X2,X3),X1)|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 7.08/7.42  cnf(c_0_47, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=X1|r1_tarski(esk5_3(X1,k2_xboole_0(X1,X2),X1),X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 7.08/7.42  cnf(c_0_48, plain, (r1_tarski(k3_xboole_0(k2_xboole_0(k3_xboole_0(X1,X2),X1),X3),k2_xboole_0(X2,X3))|~r1_tarski(k3_xboole_0(X1,X2),X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 7.08/7.42  cnf(c_0_49, negated_conjecture, (k3_xboole_0(k2_xboole_0(X1,esk12_0),esk13_0)=k2_xboole_0(X1,esk12_0)|~r1_tarski(X1,esk13_0)), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 7.08/7.42  cnf(c_0_50, plain, (k3_xboole_0(k2_xboole_0(X1,X2),X1)=X1), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_35]), c_0_42])])).
% 7.08/7.42  cnf(c_0_51, negated_conjecture, (r1_tarski(k3_xboole_0(k2_xboole_0(esk12_0,esk12_0),X1),k2_xboole_0(esk13_0,X1))|~r1_tarski(esk12_0,X1)), inference(spm,[status(thm)],[c_0_48, c_0_45])).
% 7.08/7.42  cnf(c_0_52, negated_conjecture, (k2_xboole_0(esk13_0,esk12_0)=esk13_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_35])])).
% 7.08/7.42  cnf(c_0_53, negated_conjecture, (~r1_tarski(esk12_0,esk13_0)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 7.08/7.42  cnf(c_0_54, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_50]), c_0_35])]), c_0_53]), ['proof']).
% 7.08/7.42  # SZS output end CNFRefutation
% 7.08/7.42  # Proof object total steps             : 55
% 7.08/7.42  # Proof object clause steps            : 32
% 7.08/7.42  # Proof object formula steps           : 23
% 7.08/7.42  # Proof object conjectures             : 12
% 7.08/7.42  # Proof object clause conjectures      : 9
% 7.08/7.42  # Proof object formula conjectures     : 3
% 7.08/7.42  # Proof object initial clauses used    : 15
% 7.08/7.42  # Proof object initial formulas used   : 11
% 7.08/7.42  # Proof object generating inferences   : 16
% 7.08/7.42  # Proof object simplifying inferences  : 11
% 7.08/7.42  # Training examples: 0 positive, 0 negative
% 7.08/7.42  # Parsed axioms                        : 30
% 7.08/7.42  # Removed by relevancy pruning/SinE    : 0
% 7.08/7.42  # Initial clauses                      : 52
% 7.08/7.42  # Removed in clause preprocessing      : 0
% 7.08/7.42  # Initial clauses in saturation        : 52
% 7.08/7.42  # Processed clauses                    : 12963
% 7.08/7.42  # ...of these trivial                  : 166
% 7.08/7.42  # ...subsumed                          : 10213
% 7.08/7.42  # ...remaining for further processing  : 2584
% 7.08/7.42  # Other redundant clauses eliminated   : 2
% 7.08/7.42  # Clauses deleted for lack of memory   : 0
% 7.08/7.42  # Backward-subsumed                    : 132
% 7.08/7.42  # Backward-rewritten                   : 183
% 7.08/7.42  # Generated clauses                    : 504049
% 7.08/7.42  # ...of the previous two non-trivial   : 468215
% 7.08/7.42  # Contextual simplify-reflections      : 73
% 7.08/7.42  # Paramodulations                      : 503996
% 7.08/7.42  # Factorizations                       : 51
% 7.08/7.42  # Equation resolutions                 : 2
% 7.08/7.42  # Propositional unsat checks           : 0
% 7.08/7.42  #    Propositional check models        : 0
% 7.08/7.42  #    Propositional check unsatisfiable : 0
% 7.08/7.42  #    Propositional clauses             : 0
% 7.08/7.42  #    Propositional clauses after purity: 0
% 7.08/7.42  #    Propositional unsat core size     : 0
% 7.08/7.42  #    Propositional preprocessing time  : 0.000
% 7.08/7.42  #    Propositional encoding time       : 0.000
% 7.08/7.42  #    Propositional solver time         : 0.000
% 7.08/7.42  #    Success case prop preproc time    : 0.000
% 7.08/7.42  #    Success case prop encoding time   : 0.000
% 7.08/7.42  #    Success case prop solver time     : 0.000
% 7.08/7.42  # Current number of processed clauses  : 2267
% 7.08/7.42  #    Positive orientable unit clauses  : 154
% 7.08/7.42  #    Positive unorientable unit clauses: 0
% 7.08/7.42  #    Negative unit clauses             : 58
% 7.08/7.42  #    Non-unit-clauses                  : 2055
% 7.08/7.42  # Current number of unprocessed clauses: 453701
% 7.08/7.42  # ...number of literals in the above   : 1780328
% 7.08/7.42  # Current number of archived formulas  : 0
% 7.08/7.42  # Current number of archived clauses   : 315
% 7.08/7.42  # Clause-clause subsumption calls (NU) : 487224
% 7.08/7.42  # Rec. Clause-clause subsumption calls : 304073
% 7.08/7.42  # Non-unit clause-clause subsumptions  : 5462
% 7.08/7.42  # Unit Clause-clause subsumption calls : 19628
% 7.08/7.42  # Rewrite failures with RHS unbound    : 0
% 7.08/7.42  # BW rewrite match attempts            : 1003
% 7.08/7.42  # BW rewrite match successes           : 58
% 7.08/7.42  # Condensation attempts                : 0
% 7.08/7.42  # Condensation successes               : 0
% 7.08/7.42  # Termbank termtop insertions          : 10246352
% 7.17/7.44  
% 7.17/7.44  # -------------------------------------------------
% 7.17/7.44  # User time                : 6.750 s
% 7.17/7.44  # System time              : 0.251 s
% 7.17/7.44  # Total time               : 7.001 s
% 7.17/7.44  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
