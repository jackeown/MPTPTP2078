%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:54:23 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   33 (  80 expanded)
%              Number of clauses        :   24 (  35 expanded)
%              Number of leaves         :    4 (  18 expanded)
%              Depth                    :   11
%              Number of atoms          :  143 ( 420 expanded)
%              Number of equality atoms :   62 ( 162 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   44 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t117_funct_1,conjecture,(
    ! [X1,X2] :
      ( ( v1_relat_1(X2)
        & v1_funct_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_funct_1)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(d12_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( X3 = k9_relat_1(X1,X2)
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r2_hidden(X5,k1_relat_1(X1))
                  & r2_hidden(X5,X2)
                  & X4 = k1_funct_1(X1,X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(d16_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] : k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(c_0_4,negated_conjecture,(
    ~ ! [X1,X2] :
        ( ( v1_relat_1(X2)
          & v1_funct_1(X2) )
       => ( r2_hidden(X1,k1_relat_1(X2))
         => k11_relat_1(X2,X1) = k1_tarski(k1_funct_1(X2,X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t117_funct_1])).

fof(c_0_5,plain,(
    ! [X6,X7,X8,X9,X10,X11] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X6
        | X7 != k1_tarski(X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k1_tarski(X6) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) != X10
        | X11 = k1_tarski(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | esk1_2(X10,X11) = X10
        | X11 = k1_tarski(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

fof(c_0_6,plain,(
    ! [X23,X24,X25,X26,X28,X29,X30,X31,X33] :
      ( ( r2_hidden(esk4_4(X23,X24,X25,X26),k1_relat_1(X23))
        | ~ r2_hidden(X26,X25)
        | X25 != k9_relat_1(X23,X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( r2_hidden(esk4_4(X23,X24,X25,X26),X24)
        | ~ r2_hidden(X26,X25)
        | X25 != k9_relat_1(X23,X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( X26 = k1_funct_1(X23,esk4_4(X23,X24,X25,X26))
        | ~ r2_hidden(X26,X25)
        | X25 != k9_relat_1(X23,X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(X29,k1_relat_1(X23))
        | ~ r2_hidden(X29,X24)
        | X28 != k1_funct_1(X23,X29)
        | r2_hidden(X28,X25)
        | X25 != k9_relat_1(X23,X24)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( ~ r2_hidden(esk5_3(X23,X30,X31),X31)
        | ~ r2_hidden(X33,k1_relat_1(X23))
        | ~ r2_hidden(X33,X30)
        | esk5_3(X23,X30,X31) != k1_funct_1(X23,X33)
        | X31 = k9_relat_1(X23,X30)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( r2_hidden(esk6_3(X23,X30,X31),k1_relat_1(X23))
        | r2_hidden(esk5_3(X23,X30,X31),X31)
        | X31 = k9_relat_1(X23,X30)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( r2_hidden(esk6_3(X23,X30,X31),X30)
        | r2_hidden(esk5_3(X23,X30,X31),X31)
        | X31 = k9_relat_1(X23,X30)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) )
      & ( esk5_3(X23,X30,X31) = k1_funct_1(X23,esk6_3(X23,X30,X31))
        | r2_hidden(esk5_3(X23,X30,X31),X31)
        | X31 = k9_relat_1(X23,X30)
        | ~ v1_relat_1(X23)
        | ~ v1_funct_1(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).

fof(c_0_7,negated_conjecture,
    ( v1_relat_1(esk8_0)
    & v1_funct_1(esk8_0)
    & r2_hidden(esk7_0,k1_relat_1(esk8_0))
    & k11_relat_1(esk8_0,esk7_0) != k1_tarski(k1_funct_1(esk8_0,esk7_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).

cnf(c_0_8,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( r2_hidden(esk6_3(X1,X2,X3),X2)
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v1_funct_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v1_relat_1(esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( esk5_3(X1,X2,X3) = k1_funct_1(X1,esk6_3(X1,X2,X3))
    | r2_hidden(esk5_3(X1,X2,X3),X3)
    | X3 = k9_relat_1(X1,X2)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_8])).

cnf(c_0_14,negated_conjecture,
    ( X1 = k9_relat_1(esk8_0,X2)
    | r2_hidden(esk6_3(esk8_0,X2,X1),X2)
    | r2_hidden(esk5_3(esk8_0,X2,X1),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11])])).

cnf(c_0_15,negated_conjecture,
    ( k1_funct_1(esk8_0,esk6_3(esk8_0,X1,X2)) = esk5_3(esk8_0,X1,X2)
    | X2 = k9_relat_1(esk8_0,X1)
    | r2_hidden(esk5_3(esk8_0,X1,X2),X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_10]),c_0_11])])).

cnf(c_0_16,negated_conjecture,
    ( esk5_3(esk8_0,X1,k1_tarski(X2)) = X2
    | k1_tarski(X2) = k9_relat_1(esk8_0,X1)
    | r2_hidden(esk6_3(esk8_0,X1,k1_tarski(X2)),X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_17,negated_conjecture,
    ( k1_funct_1(esk8_0,esk6_3(esk8_0,X1,k1_tarski(X2))) = esk5_3(esk8_0,X1,k1_tarski(X2))
    | esk5_3(esk8_0,X1,k1_tarski(X2)) = X2
    | k1_tarski(X2) = k9_relat_1(esk8_0,X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( esk5_3(esk8_0,k1_tarski(X1),k1_tarski(X2)) = X2
    | esk6_3(esk8_0,k1_tarski(X1),k1_tarski(X2)) = X1
    | k1_tarski(X2) = k9_relat_1(esk8_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( esk5_3(esk8_0,k1_tarski(X1),k1_tarski(X2)) = k1_funct_1(esk8_0,X1)
    | esk5_3(esk8_0,k1_tarski(X1),k1_tarski(X2)) = X2
    | k1_tarski(X2) = k9_relat_1(esk8_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

fof(c_0_21,plain,(
    ! [X16,X17] :
      ( ~ v1_relat_1(X16)
      | k11_relat_1(X16,X17) = k9_relat_1(X16,k1_tarski(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).

cnf(c_0_22,plain,
    ( X3 = k9_relat_1(X1,X2)
    | ~ r2_hidden(esk5_3(X1,X2,X3),X3)
    | ~ r2_hidden(X4,k1_relat_1(X1))
    | ~ r2_hidden(X4,X2)
    | esk5_3(X1,X2,X3) != k1_funct_1(X1,X4)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,negated_conjecture,
    ( esk5_3(esk8_0,k1_tarski(X1),k1_tarski(k1_funct_1(esk8_0,X1))) = k1_funct_1(esk8_0,X1)
    | k1_tarski(k1_funct_1(esk8_0,X1)) = k9_relat_1(esk8_0,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_19])])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).

cnf(c_0_25,plain,
    ( k11_relat_1(X1,X2) = k9_relat_1(X1,k1_tarski(X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk8_0,X1)) = k9_relat_1(esk8_0,k1_tarski(X1))
    | k1_funct_1(esk8_0,X1) != k1_funct_1(esk8_0,X2)
    | ~ r2_hidden(X2,k1_relat_1(esk8_0))
    | ~ r2_hidden(X2,k1_tarski(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_10]),c_0_11]),c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( k11_relat_1(esk8_0,esk7_0) != k1_tarski(k1_funct_1(esk8_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_28,negated_conjecture,
    ( k11_relat_1(esk8_0,X1) = k9_relat_1(esk8_0,k1_tarski(X1)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk8_0,X1)) = k9_relat_1(esk8_0,k1_tarski(X1))
    | ~ r2_hidden(X1,k1_relat_1(esk8_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]),c_0_24])])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(esk7_0,k1_relat_1(esk8_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_31,negated_conjecture,
    ( k1_tarski(k1_funct_1(esk8_0,esk7_0)) != k9_relat_1(esk8_0,k1_tarski(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.19/0.41  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.028 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t117_funct_1, conjecture, ![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_funct_1)).
% 0.19/0.41  fof(d1_tarski, axiom, ![X1, X2]:(X2=k1_tarski(X1)<=>![X3]:(r2_hidden(X3,X2)<=>X3=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 0.19/0.41  fof(d12_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(X3=k9_relat_1(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>?[X5]:((r2_hidden(X5,k1_relat_1(X1))&r2_hidden(X5,X2))&X4=k1_funct_1(X1,X5))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_funct_1)).
% 0.19/0.41  fof(d16_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d16_relat_1)).
% 0.19/0.41  fof(c_0_4, negated_conjecture, ~(![X1, X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(r2_hidden(X1,k1_relat_1(X2))=>k11_relat_1(X2,X1)=k1_tarski(k1_funct_1(X2,X1))))), inference(assume_negation,[status(cth)],[t117_funct_1])).
% 0.19/0.41  fof(c_0_5, plain, ![X6, X7, X8, X9, X10, X11]:(((~r2_hidden(X8,X7)|X8=X6|X7!=k1_tarski(X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k1_tarski(X6)))&((~r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)!=X10|X11=k1_tarski(X10))&(r2_hidden(esk1_2(X10,X11),X11)|esk1_2(X10,X11)=X10|X11=k1_tarski(X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).
% 0.19/0.41  fof(c_0_6, plain, ![X23, X24, X25, X26, X28, X29, X30, X31, X33]:(((((r2_hidden(esk4_4(X23,X24,X25,X26),k1_relat_1(X23))|~r2_hidden(X26,X25)|X25!=k9_relat_1(X23,X24)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(r2_hidden(esk4_4(X23,X24,X25,X26),X24)|~r2_hidden(X26,X25)|X25!=k9_relat_1(X23,X24)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(X26=k1_funct_1(X23,esk4_4(X23,X24,X25,X26))|~r2_hidden(X26,X25)|X25!=k9_relat_1(X23,X24)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(~r2_hidden(X29,k1_relat_1(X23))|~r2_hidden(X29,X24)|X28!=k1_funct_1(X23,X29)|r2_hidden(X28,X25)|X25!=k9_relat_1(X23,X24)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&((~r2_hidden(esk5_3(X23,X30,X31),X31)|(~r2_hidden(X33,k1_relat_1(X23))|~r2_hidden(X33,X30)|esk5_3(X23,X30,X31)!=k1_funct_1(X23,X33))|X31=k9_relat_1(X23,X30)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(((r2_hidden(esk6_3(X23,X30,X31),k1_relat_1(X23))|r2_hidden(esk5_3(X23,X30,X31),X31)|X31=k9_relat_1(X23,X30)|(~v1_relat_1(X23)|~v1_funct_1(X23)))&(r2_hidden(esk6_3(X23,X30,X31),X30)|r2_hidden(esk5_3(X23,X30,X31),X31)|X31=k9_relat_1(X23,X30)|(~v1_relat_1(X23)|~v1_funct_1(X23))))&(esk5_3(X23,X30,X31)=k1_funct_1(X23,esk6_3(X23,X30,X31))|r2_hidden(esk5_3(X23,X30,X31),X31)|X31=k9_relat_1(X23,X30)|(~v1_relat_1(X23)|~v1_funct_1(X23)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d12_funct_1])])])])])])).
% 0.19/0.41  fof(c_0_7, negated_conjecture, ((v1_relat_1(esk8_0)&v1_funct_1(esk8_0))&(r2_hidden(esk7_0,k1_relat_1(esk8_0))&k11_relat_1(esk8_0,esk7_0)!=k1_tarski(k1_funct_1(esk8_0,esk7_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_4])])])).
% 0.19/0.41  cnf(c_0_8, plain, (X1=X3|~r2_hidden(X1,X2)|X2!=k1_tarski(X3)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  cnf(c_0_9, plain, (r2_hidden(esk6_3(X1,X2,X3),X2)|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_10, negated_conjecture, (v1_funct_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_11, negated_conjecture, (v1_relat_1(esk8_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_12, plain, (esk5_3(X1,X2,X3)=k1_funct_1(X1,esk6_3(X1,X2,X3))|r2_hidden(esk5_3(X1,X2,X3),X3)|X3=k9_relat_1(X1,X2)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_13, plain, (X1=X2|~r2_hidden(X1,k1_tarski(X2))), inference(er,[status(thm)],[c_0_8])).
% 0.19/0.41  cnf(c_0_14, negated_conjecture, (X1=k9_relat_1(esk8_0,X2)|r2_hidden(esk6_3(esk8_0,X2,X1),X2)|r2_hidden(esk5_3(esk8_0,X2,X1),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11])])).
% 0.19/0.41  cnf(c_0_15, negated_conjecture, (k1_funct_1(esk8_0,esk6_3(esk8_0,X1,X2))=esk5_3(esk8_0,X1,X2)|X2=k9_relat_1(esk8_0,X1)|r2_hidden(esk5_3(esk8_0,X1,X2),X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_10]), c_0_11])])).
% 0.19/0.41  cnf(c_0_16, negated_conjecture, (esk5_3(esk8_0,X1,k1_tarski(X2))=X2|k1_tarski(X2)=k9_relat_1(esk8_0,X1)|r2_hidden(esk6_3(esk8_0,X1,k1_tarski(X2)),X1)), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.19/0.41  cnf(c_0_17, negated_conjecture, (k1_funct_1(esk8_0,esk6_3(esk8_0,X1,k1_tarski(X2)))=esk5_3(esk8_0,X1,k1_tarski(X2))|esk5_3(esk8_0,X1,k1_tarski(X2))=X2|k1_tarski(X2)=k9_relat_1(esk8_0,X1)), inference(spm,[status(thm)],[c_0_13, c_0_15])).
% 0.19/0.41  cnf(c_0_18, negated_conjecture, (esk5_3(esk8_0,k1_tarski(X1),k1_tarski(X2))=X2|esk6_3(esk8_0,k1_tarski(X1),k1_tarski(X2))=X1|k1_tarski(X2)=k9_relat_1(esk8_0,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_13, c_0_16])).
% 0.19/0.41  cnf(c_0_19, negated_conjecture, (esk5_3(esk8_0,k1_tarski(X1),k1_tarski(X2))=k1_funct_1(esk8_0,X1)|esk5_3(esk8_0,k1_tarski(X1),k1_tarski(X2))=X2|k1_tarski(X2)=k9_relat_1(esk8_0,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.19/0.41  cnf(c_0_20, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k1_tarski(X2)), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.19/0.41  fof(c_0_21, plain, ![X16, X17]:(~v1_relat_1(X16)|k11_relat_1(X16,X17)=k9_relat_1(X16,k1_tarski(X17))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_relat_1])])])).
% 0.19/0.41  cnf(c_0_22, plain, (X3=k9_relat_1(X1,X2)|~r2_hidden(esk5_3(X1,X2,X3),X3)|~r2_hidden(X4,k1_relat_1(X1))|~r2_hidden(X4,X2)|esk5_3(X1,X2,X3)!=k1_funct_1(X1,X4)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.19/0.41  cnf(c_0_23, negated_conjecture, (esk5_3(esk8_0,k1_tarski(X1),k1_tarski(k1_funct_1(esk8_0,X1)))=k1_funct_1(esk8_0,X1)|k1_tarski(k1_funct_1(esk8_0,X1))=k9_relat_1(esk8_0,k1_tarski(X1))), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_19])])).
% 0.19/0.41  cnf(c_0_24, plain, (r2_hidden(X1,k1_tarski(X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_20])])).
% 0.19/0.41  cnf(c_0_25, plain, (k11_relat_1(X1,X2)=k9_relat_1(X1,k1_tarski(X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_26, negated_conjecture, (k1_tarski(k1_funct_1(esk8_0,X1))=k9_relat_1(esk8_0,k1_tarski(X1))|k1_funct_1(esk8_0,X1)!=k1_funct_1(esk8_0,X2)|~r2_hidden(X2,k1_relat_1(esk8_0))|~r2_hidden(X2,k1_tarski(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_10]), c_0_11]), c_0_24])])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (k11_relat_1(esk8_0,esk7_0)!=k1_tarski(k1_funct_1(esk8_0,esk7_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_28, negated_conjecture, (k11_relat_1(esk8_0,X1)=k9_relat_1(esk8_0,k1_tarski(X1))), inference(spm,[status(thm)],[c_0_25, c_0_11])).
% 0.19/0.41  cnf(c_0_29, negated_conjecture, (k1_tarski(k1_funct_1(esk8_0,X1))=k9_relat_1(esk8_0,k1_tarski(X1))|~r2_hidden(X1,k1_relat_1(esk8_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_26]), c_0_24])])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (r2_hidden(esk7_0,k1_relat_1(esk8_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.19/0.41  cnf(c_0_31, negated_conjecture, (k1_tarski(k1_funct_1(esk8_0,esk7_0))!=k9_relat_1(esk8_0,k1_tarski(esk7_0))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.41  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 33
% 0.19/0.41  # Proof object clause steps            : 24
% 0.19/0.41  # Proof object formula steps           : 9
% 0.19/0.41  # Proof object conjectures             : 19
% 0.19/0.41  # Proof object clause conjectures      : 16
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 10
% 0.19/0.41  # Proof object initial formulas used   : 4
% 0.19/0.41  # Proof object generating inferences   : 11
% 0.19/0.41  # Proof object simplifying inferences  : 16
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 7
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 26
% 0.19/0.41  # Removed in clause preprocessing      : 0
% 0.19/0.41  # Initial clauses in saturation        : 26
% 0.19/0.41  # Processed clauses                    : 262
% 0.19/0.41  # ...of these trivial                  : 10
% 0.19/0.41  # ...subsumed                          : 22
% 0.19/0.41  # ...remaining for further processing  : 230
% 0.19/0.41  # Other redundant clauses eliminated   : 21
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 1
% 0.19/0.41  # Backward-rewritten                   : 22
% 0.19/0.41  # Generated clauses                    : 903
% 0.19/0.41  # ...of the previous two non-trivial   : 781
% 0.19/0.41  # Contextual simplify-reflections      : 0
% 0.19/0.41  # Paramodulations                      : 879
% 0.19/0.41  # Factorizations                       : 4
% 0.19/0.41  # Equation resolutions                 : 22
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
% 0.19/0.41  # Current number of processed clauses  : 174
% 0.19/0.41  #    Positive orientable unit clauses  : 23
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 1
% 0.19/0.41  #    Non-unit-clauses                  : 150
% 0.19/0.41  # Current number of unprocessed clauses: 560
% 0.19/0.41  # ...number of literals in the above   : 2646
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 49
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 2566
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 683
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 23
% 0.19/0.41  # Unit Clause-clause subsumption calls : 35
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 13
% 0.19/0.41  # BW rewrite match successes           : 7
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 34584
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.065 s
% 0.19/0.41  # System time              : 0.005 s
% 0.19/0.41  # Total time               : 0.070 s
% 0.19/0.41  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
