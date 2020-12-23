%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:48:11 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 255 expanded)
%              Number of clauses        :   42 ( 121 expanded)
%              Number of leaves         :    7 (  63 expanded)
%              Depth                    :   12
%              Number of atoms          :  154 ( 627 expanded)
%              Number of equality atoms :   85 ( 419 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t34_zfmisc_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))
    <=> ( X1 = X3
        & X2 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t35_zfmisc_1,axiom,(
    ! [X1,X2] : k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

fof(t23_relat_1,conjecture,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( X3 = k1_tarski(k4_tarski(X1,X2))
       => ( k1_relat_1(X3) = k1_tarski(X1)
          & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_relat_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d5_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k2_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X4,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(c_0_7,plain,(
    ! [X99,X100,X101,X102] :
      ( ( X99 = X101
        | ~ r2_hidden(k4_tarski(X99,X100),k2_zfmisc_1(k1_tarski(X101),k1_tarski(X102))) )
      & ( X100 = X102
        | ~ r2_hidden(k4_tarski(X99,X100),k2_zfmisc_1(k1_tarski(X101),k1_tarski(X102))) )
      & ( X99 != X101
        | X100 != X102
        | r2_hidden(k4_tarski(X99,X100),k2_zfmisc_1(k1_tarski(X101),k1_tarski(X102))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).

fof(c_0_8,plain,(
    ! [X78] : k2_tarski(X78,X78) = k1_tarski(X78) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_9,plain,(
    ! [X103,X104] : k2_zfmisc_1(k1_tarski(X103),k1_tarski(X104)) = k1_tarski(k4_tarski(X103,X104)) ),
    inference(variable_rename,[status(thm)],[t35_zfmisc_1])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1,X2,X3] :
        ( v1_relat_1(X3)
       => ( X3 = k1_tarski(k4_tarski(X1,X2))
         => ( k1_relat_1(X3) = k1_tarski(X1)
            & k2_relat_1(X3) = k1_tarski(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_relat_1])).

cnf(c_0_11,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2)) = k1_tarski(k4_tarski(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk18_0)
    & esk18_0 = k1_tarski(k4_tarski(esk16_0,esk17_0))
    & ( k1_relat_1(esk18_0) != k1_tarski(esk16_0)
      | k2_relat_1(esk18_0) != k1_tarski(esk17_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_15,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X4,X4))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11,c_0_12]),c_0_12])).

cnf(c_0_16,plain,
    ( k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2)) = k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13,c_0_12]),c_0_12]),c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk18_0 = k1_tarski(k4_tarski(esk16_0,esk17_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X117,X118,X119,X121,X122,X123,X124,X126] :
      ( ( ~ r2_hidden(X119,X118)
        | r2_hidden(k4_tarski(X119,esk10_3(X117,X118,X119)),X117)
        | X118 != k1_relat_1(X117) )
      & ( ~ r2_hidden(k4_tarski(X121,X122),X117)
        | r2_hidden(X121,X118)
        | X118 != k1_relat_1(X117) )
      & ( ~ r2_hidden(esk11_2(X123,X124),X124)
        | ~ r2_hidden(k4_tarski(esk11_2(X123,X124),X126),X123)
        | X124 = k1_relat_1(X123) )
      & ( r2_hidden(esk11_2(X123,X124),X124)
        | r2_hidden(k4_tarski(esk11_2(X123,X124),esk12_2(X123,X124)),X123)
        | X124 = k1_relat_1(X123) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

fof(c_0_19,plain,(
    ! [X69,X70,X71,X72,X73,X74] :
      ( ( ~ r2_hidden(X71,X70)
        | X71 = X69
        | X70 != k1_tarski(X69) )
      & ( X72 != X69
        | r2_hidden(X72,X70)
        | X70 != k1_tarski(X69) )
      & ( ~ r2_hidden(esk7_2(X73,X74),X74)
        | esk7_2(X73,X74) != X73
        | X74 = k1_tarski(X73) )
      & ( r2_hidden(esk7_2(X73,X74),X74)
        | esk7_2(X73,X74) = X73
        | X74 = k1_tarski(X73) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_20,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X1,X3),k2_tarski(k4_tarski(X2,X4),k4_tarski(X2,X4))) ),
    inference(rw,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( esk18_0 = k2_tarski(k4_tarski(esk16_0,esk17_0),k4_tarski(esk16_0,esk17_0)) ),
    inference(rw,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_22,plain,
    ( r2_hidden(k4_tarski(X1,esk10_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_tarski(X4),k1_tarski(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk16_0
    | ~ r2_hidden(k4_tarski(X1,X2),esk18_0) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_26,plain,
    ( r2_hidden(k4_tarski(X1,esk10_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_22])).

cnf(c_0_27,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | esk7_2(X1,X2) = X1
    | X2 = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X2) ),
    inference(rw,[status(thm)],[c_0_23,c_0_12])).

cnf(c_0_29,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k2_tarski(X4,X4),k2_tarski(X2,X2))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24,c_0_12]),c_0_12])).

fof(c_0_30,plain,(
    ! [X128,X129,X130,X132,X133,X134,X135,X137] :
      ( ( ~ r2_hidden(X130,X129)
        | r2_hidden(k4_tarski(esk13_3(X128,X129,X130),X130),X128)
        | X129 != k2_relat_1(X128) )
      & ( ~ r2_hidden(k4_tarski(X133,X132),X128)
        | r2_hidden(X132,X129)
        | X129 != k2_relat_1(X128) )
      & ( ~ r2_hidden(esk14_2(X134,X135),X135)
        | ~ r2_hidden(k4_tarski(X137,esk14_2(X134,X135)),X134)
        | X135 = k2_relat_1(X134) )
      & ( r2_hidden(esk14_2(X134,X135),X135)
        | r2_hidden(k4_tarski(esk15_2(X134,X135),esk14_2(X134,X135)),X134)
        | X135 = k2_relat_1(X134) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).

cnf(c_0_31,negated_conjecture,
    ( X1 = esk16_0
    | ~ r2_hidden(X1,k1_relat_1(esk18_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_32,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk7_2(X1,X2) = X1
    | r2_hidden(esk7_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_27,c_0_12])).

cnf(c_0_33,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,plain,
    ( r2_hidden(X1,k2_tarski(X1,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).

cnf(c_0_35,plain,
    ( X1 = X2
    | ~ r2_hidden(k4_tarski(X3,X1),k2_tarski(k4_tarski(X4,X2),k4_tarski(X4,X2))) ),
    inference(rw,[status(thm)],[c_0_29,c_0_16])).

cnf(c_0_36,plain,
    ( r2_hidden(k4_tarski(esk13_3(X3,X2,X1),X1),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( X2 = k1_tarski(X1)
    | ~ r2_hidden(esk7_2(X1,X2),X2)
    | esk7_2(X1,X2) != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_38,negated_conjecture,
    ( esk7_2(X1,k1_relat_1(esk18_0)) = esk16_0
    | esk7_2(X1,k1_relat_1(esk18_0)) = X1
    | k1_relat_1(esk18_0) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X1,X3),X2) ),
    inference(er,[status(thm)],[c_0_33])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(k4_tarski(esk16_0,esk17_0),esk18_0) ),
    inference(spm,[status(thm)],[c_0_34,c_0_21])).

cnf(c_0_41,negated_conjecture,
    ( X1 = esk17_0
    | ~ r2_hidden(k4_tarski(X2,X1),esk18_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_21])).

cnf(c_0_42,plain,
    ( r2_hidden(k4_tarski(esk13_3(X1,k2_relat_1(X1),X2),X2),X1)
    | ~ r2_hidden(X2,k2_relat_1(X1)) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( k1_relat_1(esk18_0) != k1_tarski(esk16_0)
    | k2_relat_1(esk18_0) != k1_tarski(esk17_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_44,plain,
    ( X2 = k2_tarski(X1,X1)
    | esk7_2(X1,X2) != X1
    | ~ r2_hidden(esk7_2(X1,X2),X2) ),
    inference(rw,[status(thm)],[c_0_37,c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( k1_relat_1(esk18_0) = k2_tarski(esk16_0,esk16_0)
    | esk7_2(esk16_0,k1_relat_1(esk18_0)) = esk16_0 ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_38])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk16_0,k1_relat_1(esk18_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( X1 = esk17_0
    | ~ r2_hidden(X1,k2_relat_1(esk18_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( k1_relat_1(esk18_0) != k2_tarski(esk16_0,esk16_0)
    | k2_relat_1(esk18_0) != k2_tarski(esk17_0,esk17_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_12]),c_0_12])).

cnf(c_0_49,negated_conjecture,
    ( k1_relat_1(esk18_0) = k2_tarski(esk16_0,esk16_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46])])).

cnf(c_0_50,plain,
    ( r2_hidden(X2,X4)
    | ~ r2_hidden(k4_tarski(X1,X2),X3)
    | X4 != k2_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_51,negated_conjecture,
    ( esk7_2(X1,k2_relat_1(esk18_0)) = esk17_0
    | esk7_2(X1,k2_relat_1(esk18_0)) = X1
    | k2_relat_1(esk18_0) = k2_tarski(X1,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_32])).

cnf(c_0_52,negated_conjecture,
    ( k2_relat_1(esk18_0) != k2_tarski(esk17_0,esk17_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48,c_0_49])])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k2_relat_1(X2))
    | ~ r2_hidden(k4_tarski(X3,X1),X2) ),
    inference(er,[status(thm)],[c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( esk7_2(esk17_0,k2_relat_1(esk18_0)) = esk17_0 ),
    inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_51])]),c_0_52])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk17_0,k2_relat_1(esk18_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_40])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_54]),c_0_55])]),c_0_52]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:15:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 1.63/1.80  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_RG_S04BN
% 1.63/1.80  # and selection function PSelectComplexExceptUniqMaxHorn.
% 1.63/1.80  #
% 1.63/1.80  # Preprocessing time       : 0.031 s
% 1.63/1.80  # Presaturation interreduction done
% 1.63/1.80  
% 1.63/1.80  # Proof found!
% 1.63/1.80  # SZS status Theorem
% 1.63/1.80  # SZS output start CNFRefutation
% 1.63/1.80  fof(t34_zfmisc_1, axiom, ![X1, X2, X3, X4]:(r2_hidden(k4_tarski(X1,X2),k2_zfmisc_1(k1_tarski(X3),k1_tarski(X4)))<=>(X1=X3&X2=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 1.63/1.80  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.63/1.80  fof(t35_zfmisc_1, axiom, ![X1, X2]:k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 1.63/1.80  fof(t23_relat_1, conjecture, ![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_relat_1)).
% 1.63/1.80  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.63/1.80  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.63/1.80  fof(d5_relat_1, axiom, ![X1, X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X4,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 1.63/1.80  fof(c_0_7, plain, ![X99, X100, X101, X102]:(((X99=X101|~r2_hidden(k4_tarski(X99,X100),k2_zfmisc_1(k1_tarski(X101),k1_tarski(X102))))&(X100=X102|~r2_hidden(k4_tarski(X99,X100),k2_zfmisc_1(k1_tarski(X101),k1_tarski(X102)))))&(X99!=X101|X100!=X102|r2_hidden(k4_tarski(X99,X100),k2_zfmisc_1(k1_tarski(X101),k1_tarski(X102))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_zfmisc_1])])])).
% 1.63/1.80  fof(c_0_8, plain, ![X78]:k2_tarski(X78,X78)=k1_tarski(X78), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 1.63/1.80  fof(c_0_9, plain, ![X103, X104]:k2_zfmisc_1(k1_tarski(X103),k1_tarski(X104))=k1_tarski(k4_tarski(X103,X104)), inference(variable_rename,[status(thm)],[t35_zfmisc_1])).
% 1.63/1.80  fof(c_0_10, negated_conjecture, ~(![X1, X2, X3]:(v1_relat_1(X3)=>(X3=k1_tarski(k4_tarski(X1,X2))=>(k1_relat_1(X3)=k1_tarski(X1)&k2_relat_1(X3)=k1_tarski(X2))))), inference(assume_negation,[status(cth)],[t23_relat_1])).
% 1.63/1.80  cnf(c_0_11, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k1_tarski(X2),k1_tarski(X4)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.63/1.80  cnf(c_0_12, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 1.63/1.80  cnf(c_0_13, plain, (k2_zfmisc_1(k1_tarski(X1),k1_tarski(X2))=k1_tarski(k4_tarski(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 1.63/1.80  fof(c_0_14, negated_conjecture, (v1_relat_1(esk18_0)&(esk18_0=k1_tarski(k4_tarski(esk16_0,esk17_0))&(k1_relat_1(esk18_0)!=k1_tarski(esk16_0)|k2_relat_1(esk18_0)!=k1_tarski(esk17_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 1.63/1.80  cnf(c_0_15, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_zfmisc_1(k2_tarski(X2,X2),k2_tarski(X4,X4)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_11, c_0_12]), c_0_12])).
% 1.63/1.80  cnf(c_0_16, plain, (k2_zfmisc_1(k2_tarski(X1,X1),k2_tarski(X2,X2))=k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X2))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_13, c_0_12]), c_0_12]), c_0_12])).
% 1.63/1.80  cnf(c_0_17, negated_conjecture, (esk18_0=k1_tarski(k4_tarski(esk16_0,esk17_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.63/1.80  fof(c_0_18, plain, ![X117, X118, X119, X121, X122, X123, X124, X126]:(((~r2_hidden(X119,X118)|r2_hidden(k4_tarski(X119,esk10_3(X117,X118,X119)),X117)|X118!=k1_relat_1(X117))&(~r2_hidden(k4_tarski(X121,X122),X117)|r2_hidden(X121,X118)|X118!=k1_relat_1(X117)))&((~r2_hidden(esk11_2(X123,X124),X124)|~r2_hidden(k4_tarski(esk11_2(X123,X124),X126),X123)|X124=k1_relat_1(X123))&(r2_hidden(esk11_2(X123,X124),X124)|r2_hidden(k4_tarski(esk11_2(X123,X124),esk12_2(X123,X124)),X123)|X124=k1_relat_1(X123)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 1.63/1.80  fof(c_0_19, plain, ![X69, X70, X71, X72, X73, X74]:(((~r2_hidden(X71,X70)|X71=X69|X70!=k1_tarski(X69))&(X72!=X69|r2_hidden(X72,X70)|X70!=k1_tarski(X69)))&((~r2_hidden(esk7_2(X73,X74),X74)|esk7_2(X73,X74)!=X73|X74=k1_tarski(X73))&(r2_hidden(esk7_2(X73,X74),X74)|esk7_2(X73,X74)=X73|X74=k1_tarski(X73)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 1.63/1.80  cnf(c_0_20, plain, (X1=X2|~r2_hidden(k4_tarski(X1,X3),k2_tarski(k4_tarski(X2,X4),k4_tarski(X2,X4)))), inference(rw,[status(thm)],[c_0_15, c_0_16])).
% 1.63/1.80  cnf(c_0_21, negated_conjecture, (esk18_0=k2_tarski(k4_tarski(esk16_0,esk17_0),k4_tarski(esk16_0,esk17_0))), inference(rw,[status(thm)],[c_0_17, c_0_12])).
% 1.63/1.80  cnf(c_0_22, plain, (r2_hidden(k4_tarski(X1,esk10_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.63/1.80  cnf(c_0_23, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.63/1.80  cnf(c_0_24, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k1_tarski(X4),k1_tarski(X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 1.63/1.80  cnf(c_0_25, negated_conjecture, (X1=esk16_0|~r2_hidden(k4_tarski(X1,X2),esk18_0)), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 1.63/1.80  cnf(c_0_26, plain, (r2_hidden(k4_tarski(X1,esk10_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_22])).
% 1.63/1.80  cnf(c_0_27, plain, (r2_hidden(esk7_2(X1,X2),X2)|esk7_2(X1,X2)=X1|X2=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.63/1.80  cnf(c_0_28, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X2,X2)), inference(rw,[status(thm)],[c_0_23, c_0_12])).
% 1.63/1.80  cnf(c_0_29, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_zfmisc_1(k2_tarski(X4,X4),k2_tarski(X2,X2)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_24, c_0_12]), c_0_12])).
% 1.63/1.80  fof(c_0_30, plain, ![X128, X129, X130, X132, X133, X134, X135, X137]:(((~r2_hidden(X130,X129)|r2_hidden(k4_tarski(esk13_3(X128,X129,X130),X130),X128)|X129!=k2_relat_1(X128))&(~r2_hidden(k4_tarski(X133,X132),X128)|r2_hidden(X132,X129)|X129!=k2_relat_1(X128)))&((~r2_hidden(esk14_2(X134,X135),X135)|~r2_hidden(k4_tarski(X137,esk14_2(X134,X135)),X134)|X135=k2_relat_1(X134))&(r2_hidden(esk14_2(X134,X135),X135)|r2_hidden(k4_tarski(esk15_2(X134,X135),esk14_2(X134,X135)),X134)|X135=k2_relat_1(X134)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_relat_1])])])])])])).
% 1.63/1.80  cnf(c_0_31, negated_conjecture, (X1=esk16_0|~r2_hidden(X1,k1_relat_1(esk18_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 1.63/1.80  cnf(c_0_32, plain, (X2=k2_tarski(X1,X1)|esk7_2(X1,X2)=X1|r2_hidden(esk7_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_27, c_0_12])).
% 1.63/1.80  cnf(c_0_33, plain, (r2_hidden(X1,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 1.63/1.80  cnf(c_0_34, plain, (r2_hidden(X1,k2_tarski(X1,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_28])])).
% 1.63/1.80  cnf(c_0_35, plain, (X1=X2|~r2_hidden(k4_tarski(X3,X1),k2_tarski(k4_tarski(X4,X2),k4_tarski(X4,X2)))), inference(rw,[status(thm)],[c_0_29, c_0_16])).
% 1.63/1.80  cnf(c_0_36, plain, (r2_hidden(k4_tarski(esk13_3(X3,X2,X1),X1),X3)|~r2_hidden(X1,X2)|X2!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.63/1.80  cnf(c_0_37, plain, (X2=k1_tarski(X1)|~r2_hidden(esk7_2(X1,X2),X2)|esk7_2(X1,X2)!=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 1.63/1.80  cnf(c_0_38, negated_conjecture, (esk7_2(X1,k1_relat_1(esk18_0))=esk16_0|esk7_2(X1,k1_relat_1(esk18_0))=X1|k1_relat_1(esk18_0)=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 1.63/1.80  cnf(c_0_39, plain, (r2_hidden(X1,k1_relat_1(X2))|~r2_hidden(k4_tarski(X1,X3),X2)), inference(er,[status(thm)],[c_0_33])).
% 1.63/1.80  cnf(c_0_40, negated_conjecture, (r2_hidden(k4_tarski(esk16_0,esk17_0),esk18_0)), inference(spm,[status(thm)],[c_0_34, c_0_21])).
% 1.63/1.80  cnf(c_0_41, negated_conjecture, (X1=esk17_0|~r2_hidden(k4_tarski(X2,X1),esk18_0)), inference(spm,[status(thm)],[c_0_35, c_0_21])).
% 1.63/1.80  cnf(c_0_42, plain, (r2_hidden(k4_tarski(esk13_3(X1,k2_relat_1(X1),X2),X2),X1)|~r2_hidden(X2,k2_relat_1(X1))), inference(er,[status(thm)],[c_0_36])).
% 1.63/1.80  cnf(c_0_43, negated_conjecture, (k1_relat_1(esk18_0)!=k1_tarski(esk16_0)|k2_relat_1(esk18_0)!=k1_tarski(esk17_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 1.63/1.80  cnf(c_0_44, plain, (X2=k2_tarski(X1,X1)|esk7_2(X1,X2)!=X1|~r2_hidden(esk7_2(X1,X2),X2)), inference(rw,[status(thm)],[c_0_37, c_0_12])).
% 1.63/1.80  cnf(c_0_45, negated_conjecture, (k1_relat_1(esk18_0)=k2_tarski(esk16_0,esk16_0)|esk7_2(esk16_0,k1_relat_1(esk18_0))=esk16_0), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_38])])).
% 1.63/1.80  cnf(c_0_46, negated_conjecture, (r2_hidden(esk16_0,k1_relat_1(esk18_0))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 1.63/1.80  cnf(c_0_47, negated_conjecture, (X1=esk17_0|~r2_hidden(X1,k2_relat_1(esk18_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 1.63/1.80  cnf(c_0_48, negated_conjecture, (k1_relat_1(esk18_0)!=k2_tarski(esk16_0,esk16_0)|k2_relat_1(esk18_0)!=k2_tarski(esk17_0,esk17_0)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_12]), c_0_12])).
% 1.63/1.80  cnf(c_0_49, negated_conjecture, (k1_relat_1(esk18_0)=k2_tarski(esk16_0,esk16_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46])])).
% 1.63/1.80  cnf(c_0_50, plain, (r2_hidden(X2,X4)|~r2_hidden(k4_tarski(X1,X2),X3)|X4!=k2_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 1.63/1.80  cnf(c_0_51, negated_conjecture, (esk7_2(X1,k2_relat_1(esk18_0))=esk17_0|esk7_2(X1,k2_relat_1(esk18_0))=X1|k2_relat_1(esk18_0)=k2_tarski(X1,X1)), inference(spm,[status(thm)],[c_0_47, c_0_32])).
% 1.63/1.80  cnf(c_0_52, negated_conjecture, (k2_relat_1(esk18_0)!=k2_tarski(esk17_0,esk17_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_48, c_0_49])])).
% 1.63/1.80  cnf(c_0_53, plain, (r2_hidden(X1,k2_relat_1(X2))|~r2_hidden(k4_tarski(X3,X1),X2)), inference(er,[status(thm)],[c_0_50])).
% 1.63/1.80  cnf(c_0_54, negated_conjecture, (esk7_2(esk17_0,k2_relat_1(esk18_0))=esk17_0), inference(sr,[status(thm)],[inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_51])]), c_0_52])).
% 1.63/1.80  cnf(c_0_55, negated_conjecture, (r2_hidden(esk17_0,k2_relat_1(esk18_0))), inference(spm,[status(thm)],[c_0_53, c_0_40])).
% 1.63/1.80  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_54]), c_0_55])]), c_0_52]), ['proof']).
% 1.63/1.80  # SZS output end CNFRefutation
% 1.63/1.80  # Proof object total steps             : 57
% 1.63/1.80  # Proof object clause steps            : 42
% 1.63/1.80  # Proof object formula steps           : 15
% 1.63/1.80  # Proof object conjectures             : 21
% 1.63/1.80  # Proof object clause conjectures      : 18
% 1.63/1.80  # Proof object formula conjectures     : 3
% 1.63/1.80  # Proof object initial clauses used    : 13
% 1.63/1.80  # Proof object initial formulas used   : 7
% 1.63/1.80  # Proof object generating inferences   : 13
% 1.63/1.80  # Proof object simplifying inferences  : 31
% 1.63/1.80  # Training examples: 0 positive, 0 negative
% 1.63/1.80  # Parsed axioms                        : 42
% 1.63/1.80  # Removed by relevancy pruning/SinE    : 0
% 1.63/1.80  # Initial clauses                      : 81
% 1.63/1.80  # Removed in clause preprocessing      : 2
% 1.63/1.80  # Initial clauses in saturation        : 79
% 1.63/1.80  # Processed clauses                    : 9082
% 1.63/1.80  # ...of these trivial                  : 50
% 1.63/1.80  # ...subsumed                          : 7392
% 1.63/1.80  # ...remaining for further processing  : 1640
% 1.63/1.80  # Other redundant clauses eliminated   : 2039
% 1.63/1.80  # Clauses deleted for lack of memory   : 0
% 1.63/1.80  # Backward-subsumed                    : 21
% 1.63/1.80  # Backward-rewritten                   : 76
% 1.63/1.80  # Generated clauses                    : 151349
% 1.63/1.80  # ...of the previous two non-trivial   : 134901
% 1.63/1.80  # Contextual simplify-reflections      : 12
% 1.63/1.80  # Paramodulations                      : 149180
% 1.63/1.80  # Factorizations                       : 126
% 1.63/1.80  # Equation resolutions                 : 2043
% 1.63/1.80  # Propositional unsat checks           : 0
% 1.63/1.80  #    Propositional check models        : 0
% 1.63/1.80  #    Propositional check unsatisfiable : 0
% 1.63/1.80  #    Propositional clauses             : 0
% 1.63/1.80  #    Propositional clauses after purity: 0
% 1.63/1.80  #    Propositional unsat core size     : 0
% 1.63/1.80  #    Propositional preprocessing time  : 0.000
% 1.63/1.80  #    Propositional encoding time       : 0.000
% 1.63/1.80  #    Propositional solver time         : 0.000
% 1.63/1.80  #    Success case prop preproc time    : 0.000
% 1.63/1.80  #    Success case prop encoding time   : 0.000
% 1.63/1.80  #    Success case prop solver time     : 0.000
% 1.63/1.80  # Current number of processed clauses  : 1446
% 1.63/1.80  #    Positive orientable unit clauses  : 96
% 1.63/1.80  #    Positive unorientable unit clauses: 6
% 1.63/1.80  #    Negative unit clauses             : 133
% 1.63/1.80  #    Non-unit-clauses                  : 1211
% 1.63/1.80  # Current number of unprocessed clauses: 125886
% 1.63/1.80  # ...number of literals in the above   : 591274
% 1.63/1.80  # Current number of archived formulas  : 0
% 1.63/1.80  # Current number of archived clauses   : 178
% 1.63/1.80  # Clause-clause subsumption calls (NU) : 125308
% 1.63/1.80  # Rec. Clause-clause subsumption calls : 90630
% 1.63/1.80  # Non-unit clause-clause subsumptions  : 2587
% 1.63/1.80  # Unit Clause-clause subsumption calls : 5943
% 1.63/1.80  # Rewrite failures with RHS unbound    : 0
% 1.63/1.80  # BW rewrite match attempts            : 140
% 1.63/1.80  # BW rewrite match successes           : 82
% 1.63/1.80  # Condensation attempts                : 0
% 1.63/1.80  # Condensation successes               : 0
% 1.63/1.80  # Termbank termtop insertions          : 2472092
% 1.63/1.80  
% 1.63/1.80  # -------------------------------------------------
% 1.63/1.80  # User time                : 1.389 s
% 1.63/1.80  # System time              : 0.072 s
% 1.63/1.80  # Total time               : 1.461 s
% 1.63/1.80  # Maximum resident set size: 1616 pages
%------------------------------------------------------------------------------
