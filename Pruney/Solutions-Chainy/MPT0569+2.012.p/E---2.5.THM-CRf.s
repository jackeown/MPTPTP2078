%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:51:34 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 202 expanded)
%              Number of clauses        :   31 (  94 expanded)
%              Number of leaves         :    8 (  51 expanded)
%              Depth                    :   12
%              Number of atoms          :  163 ( 684 expanded)
%              Number of equality atoms :   32 ( 148 expanded)
%              Maximal formula depth    :   19 (   4 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l24_zfmisc_1,axiom,(
    ! [X1,X2] :
      ~ ( r1_xboole_0(k1_tarski(X1),X2)
        & r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(t65_xboole_1,axiom,(
    ! [X1] : r1_xboole_0(X1,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(t173_relat_1,conjecture,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k10_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(t166_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(X1,k10_relat_1(X3,X2))
      <=> ? [X4] :
            ( r2_hidden(X4,k2_relat_1(X3))
            & r2_hidden(k4_tarski(X1,X4),X3)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(d14_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2,X3] :
          ( X3 = k10_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(k4_tarski(X4,X5),X1)
                  & r2_hidden(X5,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(c_0_8,plain,(
    ! [X33,X34] :
      ( ~ r1_xboole_0(k1_tarski(X33),X34)
      | ~ r2_hidden(X33,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).

fof(c_0_9,plain,(
    ! [X27] : r1_xboole_0(X27,k1_xboole_0) ),
    inference(variable_rename,[status(thm)],[t65_xboole_1])).

cnf(c_0_10,plain,
    ( ~ r1_xboole_0(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,plain,
    ( r1_xboole_0(X1,k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_12,plain,(
    ! [X49,X50,X51,X53,X54,X55,X56,X58] :
      ( ( ~ r2_hidden(X51,X50)
        | r2_hidden(k4_tarski(esk7_3(X49,X50,X51),X51),X49)
        | X50 != k2_relat_1(X49) )
      & ( ~ r2_hidden(k4_tarski(X54,X53),X49)
        | r2_hidden(X53,X50)
        | X50 != k2_relat_1(X49) )
      & ( ~ r2_hidden(esk8_2(X55,X56),X56)
        | ~ r2_hidden(k4_tarski(X58,esk8_2(X55,X56)),X55)
        | X56 = k2_relat_1(X55) )
      & ( r2_hidden(esk8_2(X55,X56),X56)
        | r2_hidden(k4_tarski(esk9_2(X55,X56),esk8_2(X55,X56)),X55)
        | X56 = k2_relat_1(X55) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1,X2] :
        ( v1_relat_1(X2)
       => ( k10_relat_1(X2,X1) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(X2),X1) ) ) ),
    inference(assume_negation,[status(cth)],[t173_relat_1])).

fof(c_0_14,plain,(
    ! [X60,X61,X62,X64] :
      ( ( r2_hidden(esk10_3(X60,X61,X62),k2_relat_1(X62))
        | ~ r2_hidden(X60,k10_relat_1(X62,X61))
        | ~ v1_relat_1(X62) )
      & ( r2_hidden(k4_tarski(X60,esk10_3(X60,X61,X62)),X62)
        | ~ r2_hidden(X60,k10_relat_1(X62,X61))
        | ~ v1_relat_1(X62) )
      & ( r2_hidden(esk10_3(X60,X61,X62),X61)
        | ~ r2_hidden(X60,k10_relat_1(X62,X61))
        | ~ v1_relat_1(X62) )
      & ( ~ r2_hidden(X64,k2_relat_1(X62))
        | ~ r2_hidden(k4_tarski(X60,X64),X62)
        | ~ r2_hidden(X64,X61)
        | r2_hidden(X60,k10_relat_1(X62,X61))
        | ~ v1_relat_1(X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).

cnf(c_0_15,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk9_2(X1,X2),esk8_2(X1,X2)),X1)
    | X2 = k2_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

fof(c_0_18,plain,(
    ! [X15,X16,X18,X19,X20] :
      ( ( r2_hidden(esk2_2(X15,X16),X15)
        | r1_xboole_0(X15,X16) )
      & ( r2_hidden(esk2_2(X15,X16),X16)
        | r1_xboole_0(X15,X16) )
      & ( ~ r2_hidden(X20,X18)
        | ~ r2_hidden(X20,X19)
        | ~ r1_xboole_0(X18,X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

fof(c_0_19,negated_conjecture,
    ( v1_relat_1(esk12_0)
    & ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
      | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) )
    & ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
      | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).

cnf(c_0_20,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),X2)
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk8_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk10_3(esk8_2(k1_xboole_0,k10_relat_1(X1,X2)),X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,negated_conjecture,
    ( v1_relat_1(esk12_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r2_hidden(esk10_3(X1,X2,X3),k2_relat_1(X3))
    | ~ r2_hidden(X1,k10_relat_1(X3,X2))
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | ~ r2_hidden(X1,k2_relat_1(esk12_0))
    | ~ r2_hidden(X1,esk11_0) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( k10_relat_1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(esk10_3(esk8_2(k1_xboole_0,k10_relat_1(esk12_0,X1)),X1,esk12_0),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,plain,
    ( k10_relat_1(X1,X2) = k1_xboole_0
    | r2_hidden(esk10_3(esk8_2(k1_xboole_0,k10_relat_1(X1,X2)),X2,X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0
    | ~ r2_hidden(esk10_3(esk8_2(k1_xboole_0,k10_relat_1(esk12_0,esk11_0)),esk11_0,esk12_0),k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( k10_relat_1(esk12_0,X1) = k1_xboole_0
    | r2_hidden(esk10_3(esk8_2(k1_xboole_0,k10_relat_1(esk12_0,X1)),X1,esk12_0),k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_25])).

fof(c_0_32,plain,(
    ! [X37,X38,X39,X40,X42,X43,X44,X45,X47] :
      ( ( r2_hidden(k4_tarski(X40,esk4_4(X37,X38,X39,X40)),X37)
        | ~ r2_hidden(X40,X39)
        | X39 != k10_relat_1(X37,X38)
        | ~ v1_relat_1(X37) )
      & ( r2_hidden(esk4_4(X37,X38,X39,X40),X38)
        | ~ r2_hidden(X40,X39)
        | X39 != k10_relat_1(X37,X38)
        | ~ v1_relat_1(X37) )
      & ( ~ r2_hidden(k4_tarski(X42,X43),X37)
        | ~ r2_hidden(X43,X38)
        | r2_hidden(X42,X39)
        | X39 != k10_relat_1(X37,X38)
        | ~ v1_relat_1(X37) )
      & ( ~ r2_hidden(esk5_3(X37,X44,X45),X45)
        | ~ r2_hidden(k4_tarski(esk5_3(X37,X44,X45),X47),X37)
        | ~ r2_hidden(X47,X44)
        | X45 = k10_relat_1(X37,X44)
        | ~ v1_relat_1(X37) )
      & ( r2_hidden(k4_tarski(esk5_3(X37,X44,X45),esk6_3(X37,X44,X45)),X37)
        | r2_hidden(esk5_3(X37,X44,X45),X45)
        | X45 = k10_relat_1(X37,X44)
        | ~ v1_relat_1(X37) )
      & ( r2_hidden(esk6_3(X37,X44,X45),X44)
        | r2_hidden(esk5_3(X37,X44,X45),X45)
        | X45 = k10_relat_1(X37,X44)
        | ~ v1_relat_1(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,negated_conjecture,
    ( k10_relat_1(esk12_0,esk11_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X5)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | ~ r2_hidden(X2,X4)
    | X5 != k10_relat_1(X3,X4)
    | ~ v1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( ~ r1_xboole_0(k2_relat_1(esk12_0),esk11_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34])])).

cnf(c_0_37,plain,
    ( r2_hidden(esk2_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,plain,
    ( r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,plain,
    ( r2_hidden(esk2_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k10_relat_1(X2,X3))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,X4),X2)
    | ~ r2_hidden(X4,X3) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),esk11_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),k2_relat_1(esk12_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_39])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,k10_relat_1(X2,esk11_0))
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(k4_tarski(X1,esk2_2(k2_relat_1(esk12_0),esk11_0)),X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(k4_tarski(esk7_3(esk12_0,k2_relat_1(esk12_0),esk2_2(k2_relat_1(esk12_0),esk11_0)),esk2_2(k2_relat_1(esk12_0),esk11_0)),esk12_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_34]),c_0_25])]),c_0_15]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S2mI
% 0.13/0.40  # and selection function SelectCQArNTNpEqFirst.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.029 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(l24_zfmisc_1, axiom, ![X1, X2]:~((r1_xboole_0(k1_tarski(X1),X2)&r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 0.13/0.40  fof(t65_xboole_1, axiom, ![X1]:r1_xboole_0(X1,k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 0.13/0.40  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 0.13/0.40  fof(t173_relat_1, conjecture, ![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 0.13/0.40  fof(t166_relat_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>(r2_hidden(X1,k10_relat_1(X3,X2))<=>?[X4]:((r2_hidden(X4,k2_relat_1(X3))&r2_hidden(k4_tarski(X1,X4),X3))&r2_hidden(X4,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 0.13/0.40  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.40  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.13/0.40  fof(d14_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2, X3]:(X3=k10_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:(r2_hidden(k4_tarski(X4,X5),X1)&r2_hidden(X5,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 0.13/0.40  fof(c_0_8, plain, ![X33, X34]:(~r1_xboole_0(k1_tarski(X33),X34)|~r2_hidden(X33,X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l24_zfmisc_1])])).
% 0.13/0.40  fof(c_0_9, plain, ![X27]:r1_xboole_0(X27,k1_xboole_0), inference(variable_rename,[status(thm)],[t65_xboole_1])).
% 0.13/0.40  cnf(c_0_10, plain, (~r1_xboole_0(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.40  cnf(c_0_11, plain, (r1_xboole_0(X1,k1_xboole_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.13/0.40  fof(c_0_12, plain, ![X49, X50, X51, X53, X54, X55, X56, X58]:(((~r2_hidden(X51,X50)|r2_hidden(k4_tarski(esk7_3(X49,X50,X51),X51),X49)|X50!=k2_relat_1(X49))&(~r2_hidden(k4_tarski(X54,X53),X49)|r2_hidden(X53,X50)|X50!=k2_relat_1(X49)))&((~r2_hidden(esk8_2(X55,X56),X56)|~r2_hidden(k4_tarski(X58,esk8_2(X55,X56)),X55)|X56=k2_relat_1(X55))&(r2_hidden(esk8_2(X55,X56),X56)|r2_hidden(k4_tarski(esk9_2(X55,X56),esk8_2(X55,X56)),X55)|X56=k2_relat_1(X55)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 0.13/0.40  fof(c_0_13, negated_conjecture, ~(![X1, X2]:(v1_relat_1(X2)=>(k10_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k2_relat_1(X2),X1)))), inference(assume_negation,[status(cth)],[t173_relat_1])).
% 0.13/0.40  fof(c_0_14, plain, ![X60, X61, X62, X64]:((((r2_hidden(esk10_3(X60,X61,X62),k2_relat_1(X62))|~r2_hidden(X60,k10_relat_1(X62,X61))|~v1_relat_1(X62))&(r2_hidden(k4_tarski(X60,esk10_3(X60,X61,X62)),X62)|~r2_hidden(X60,k10_relat_1(X62,X61))|~v1_relat_1(X62)))&(r2_hidden(esk10_3(X60,X61,X62),X61)|~r2_hidden(X60,k10_relat_1(X62,X61))|~v1_relat_1(X62)))&(~r2_hidden(X64,k2_relat_1(X62))|~r2_hidden(k4_tarski(X60,X64),X62)|~r2_hidden(X64,X61)|r2_hidden(X60,k10_relat_1(X62,X61))|~v1_relat_1(X62))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t166_relat_1])])])])])).
% 0.13/0.40  cnf(c_0_15, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.13/0.40  cnf(c_0_16, plain, (r2_hidden(esk8_2(X1,X2),X2)|r2_hidden(k4_tarski(esk9_2(X1,X2),esk8_2(X1,X2)),X1)|X2=k2_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_17, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.40  fof(c_0_18, plain, ![X15, X16, X18, X19, X20]:(((r2_hidden(esk2_2(X15,X16),X15)|r1_xboole_0(X15,X16))&(r2_hidden(esk2_2(X15,X16),X16)|r1_xboole_0(X15,X16)))&(~r2_hidden(X20,X18)|~r2_hidden(X20,X19)|~r1_xboole_0(X18,X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.13/0.40  fof(c_0_19, negated_conjecture, (v1_relat_1(esk12_0)&((k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0))&(k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_13])])])).
% 0.13/0.40  cnf(c_0_20, plain, (r2_hidden(esk10_3(X1,X2,X3),X2)|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_21, plain, (X1=k1_xboole_0|r2_hidden(esk8_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])).
% 0.13/0.40  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_23, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_24, plain, (k10_relat_1(X1,X2)=k1_xboole_0|r2_hidden(esk10_3(esk8_2(k1_xboole_0,k10_relat_1(X1,X2)),X2,X1),X2)|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.13/0.40  cnf(c_0_25, negated_conjecture, (v1_relat_1(esk12_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_26, plain, (r2_hidden(esk10_3(X1,X2,X3),k2_relat_1(X3))|~r2_hidden(X1,k10_relat_1(X3,X2))|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.40  cnf(c_0_27, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|~r2_hidden(X1,k2_relat_1(esk12_0))|~r2_hidden(X1,esk11_0)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.40  cnf(c_0_28, negated_conjecture, (k10_relat_1(esk12_0,X1)=k1_xboole_0|r2_hidden(esk10_3(esk8_2(k1_xboole_0,k10_relat_1(esk12_0,X1)),X1,esk12_0),X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.40  cnf(c_0_29, plain, (k10_relat_1(X1,X2)=k1_xboole_0|r2_hidden(esk10_3(esk8_2(k1_xboole_0,k10_relat_1(X1,X2)),X2,X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_26, c_0_21])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0|~r2_hidden(esk10_3(esk8_2(k1_xboole_0,k10_relat_1(esk12_0,esk11_0)),esk11_0,esk12_0),k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.13/0.40  cnf(c_0_31, negated_conjecture, (k10_relat_1(esk12_0,X1)=k1_xboole_0|r2_hidden(esk10_3(esk8_2(k1_xboole_0,k10_relat_1(esk12_0,X1)),X1,esk12_0),k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_29, c_0_25])).
% 0.13/0.40  fof(c_0_32, plain, ![X37, X38, X39, X40, X42, X43, X44, X45, X47]:((((r2_hidden(k4_tarski(X40,esk4_4(X37,X38,X39,X40)),X37)|~r2_hidden(X40,X39)|X39!=k10_relat_1(X37,X38)|~v1_relat_1(X37))&(r2_hidden(esk4_4(X37,X38,X39,X40),X38)|~r2_hidden(X40,X39)|X39!=k10_relat_1(X37,X38)|~v1_relat_1(X37)))&(~r2_hidden(k4_tarski(X42,X43),X37)|~r2_hidden(X43,X38)|r2_hidden(X42,X39)|X39!=k10_relat_1(X37,X38)|~v1_relat_1(X37)))&((~r2_hidden(esk5_3(X37,X44,X45),X45)|(~r2_hidden(k4_tarski(esk5_3(X37,X44,X45),X47),X37)|~r2_hidden(X47,X44))|X45=k10_relat_1(X37,X44)|~v1_relat_1(X37))&((r2_hidden(k4_tarski(esk5_3(X37,X44,X45),esk6_3(X37,X44,X45)),X37)|r2_hidden(esk5_3(X37,X44,X45),X45)|X45=k10_relat_1(X37,X44)|~v1_relat_1(X37))&(r2_hidden(esk6_3(X37,X44,X45),X44)|r2_hidden(esk5_3(X37,X44,X45),X45)|X45=k10_relat_1(X37,X44)|~v1_relat_1(X37))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d14_relat_1])])])])])])).
% 0.13/0.40  cnf(c_0_33, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)!=k1_xboole_0|~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.40  cnf(c_0_34, negated_conjecture, (k10_relat_1(esk12_0,esk11_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.13/0.40  cnf(c_0_35, plain, (r2_hidden(X1,X5)|~r2_hidden(k4_tarski(X1,X2),X3)|~r2_hidden(X2,X4)|X5!=k10_relat_1(X3,X4)|~v1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (~r1_xboole_0(k2_relat_1(esk12_0),esk11_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34])])).
% 0.13/0.40  cnf(c_0_37, plain, (r2_hidden(esk2_2(X1,X2),X2)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_38, plain, (r2_hidden(k4_tarski(esk7_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.40  cnf(c_0_39, plain, (r2_hidden(esk2_2(X1,X2),X1)|r1_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_40, plain, (r2_hidden(X1,k10_relat_1(X2,X3))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,X4),X2)|~r2_hidden(X4,X3)), inference(er,[status(thm)],[c_0_35])).
% 0.13/0.40  cnf(c_0_41, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),esk11_0)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.13/0.40  cnf(c_0_42, plain, (r2_hidden(k4_tarski(esk7_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_38])).
% 0.13/0.40  cnf(c_0_43, negated_conjecture, (r2_hidden(esk2_2(k2_relat_1(esk12_0),esk11_0),k2_relat_1(esk12_0))), inference(spm,[status(thm)],[c_0_36, c_0_39])).
% 0.13/0.40  cnf(c_0_44, negated_conjecture, (r2_hidden(X1,k10_relat_1(X2,esk11_0))|~v1_relat_1(X2)|~r2_hidden(k4_tarski(X1,esk2_2(k2_relat_1(esk12_0),esk11_0)),X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (r2_hidden(k4_tarski(esk7_3(esk12_0,k2_relat_1(esk12_0),esk2_2(k2_relat_1(esk12_0),esk11_0)),esk2_2(k2_relat_1(esk12_0),esk11_0)),esk12_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_34]), c_0_25])]), c_0_15]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 47
% 0.13/0.40  # Proof object clause steps            : 31
% 0.13/0.40  # Proof object formula steps           : 16
% 0.13/0.40  # Proof object conjectures             : 17
% 0.13/0.40  # Proof object clause conjectures      : 14
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 14
% 0.13/0.40  # Proof object initial formulas used   : 8
% 0.13/0.40  # Proof object generating inferences   : 14
% 0.13/0.40  # Proof object simplifying inferences  : 9
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 13
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 35
% 0.13/0.40  # Removed in clause preprocessing      : 3
% 0.13/0.40  # Initial clauses in saturation        : 32
% 0.13/0.40  # Processed clauses                    : 324
% 0.13/0.40  # ...of these trivial                  : 5
% 0.13/0.40  # ...subsumed                          : 107
% 0.13/0.40  # ...remaining for further processing  : 212
% 0.13/0.40  # Other redundant clauses eliminated   : 8
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 1
% 0.13/0.40  # Backward-rewritten                   : 22
% 0.13/0.40  # Generated clauses                    : 1190
% 0.13/0.40  # ...of the previous two non-trivial   : 1081
% 0.13/0.40  # Contextual simplify-reflections      : 0
% 0.13/0.40  # Paramodulations                      : 1178
% 0.13/0.40  # Factorizations                       : 4
% 0.13/0.40  # Equation resolutions                 : 8
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 150
% 0.13/0.40  #    Positive orientable unit clauses  : 31
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 117
% 0.13/0.40  # Current number of unprocessed clauses: 804
% 0.13/0.40  # ...number of literals in the above   : 2364
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 57
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 1823
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 1302
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 68
% 0.13/0.40  # Unit Clause-clause subsumption calls : 25
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 29
% 0.13/0.40  # BW rewrite match successes           : 3
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 23494
% 0.13/0.40  
% 0.13/0.40  # -------------------------------------------------
% 0.13/0.40  # User time                : 0.054 s
% 0.13/0.40  # System time              : 0.008 s
% 0.13/0.40  # Total time               : 0.062 s
% 0.13/0.40  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
