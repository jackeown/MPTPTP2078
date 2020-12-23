%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:55:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 ( 112 expanded)
%              Number of clauses        :   23 (  43 expanded)
%              Number of leaves         :    6 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :  145 ( 539 expanded)
%              Number of equality atoms :   12 (  24 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(d4_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( ( r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> r2_hidden(k4_tarski(X2,X3),X1) ) )
          & ( ~ r2_hidden(X2,k1_relat_1(X1))
           => ( X3 = k1_funct_1(X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(t175_funct_1,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2)
            & v5_funct_1(X2,X1) )
         => r1_tarski(k1_relat_1(X2),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_1)).

fof(d20_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ( v5_funct_1(X2,X1)
          <=> ! [X3] :
                ( r2_hidden(X3,k1_relat_1(X2))
               => r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(antisymmetry_r2_hidden,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(c_0_6,plain,(
    ! [X7,X8,X9,X10,X11] :
      ( ( ~ r1_tarski(X7,X8)
        | ~ r2_hidden(X9,X7)
        | r2_hidden(X9,X8) )
      & ( r2_hidden(esk1_2(X10,X11),X10)
        | r1_tarski(X10,X11) )
      & ( ~ r2_hidden(esk1_2(X10,X11),X11)
        | r1_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_7,plain,(
    ! [X13] : r1_tarski(k1_xboole_0,X13) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_8,plain,(
    ! [X29,X30,X31] :
      ( ( X31 != k1_funct_1(X29,X30)
        | r2_hidden(k4_tarski(X30,X31),X29)
        | ~ r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( ~ r2_hidden(k4_tarski(X30,X31),X29)
        | X31 = k1_funct_1(X29,X30)
        | ~ r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X31 != k1_funct_1(X29,X30)
        | X31 = k1_xboole_0
        | r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) )
      & ( X31 != k1_xboole_0
        | X31 = k1_funct_1(X29,X30)
        | r2_hidden(X30,k1_relat_1(X29))
        | ~ v1_relat_1(X29)
        | ~ v1_funct_1(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2)
              & v5_funct_1(X2,X1) )
           => r1_tarski(k1_relat_1(X2),k1_relat_1(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_1])).

cnf(c_0_10,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( X1 = k1_funct_1(X2,X3)
    | r2_hidden(X3,k1_relat_1(X2))
    | X1 != k1_xboole_0
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_13,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v5_funct_1(X26,X25)
        | ~ r2_hidden(X27,k1_relat_1(X26))
        | r2_hidden(k1_funct_1(X26,X27),k1_funct_1(X25,X27))
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( r2_hidden(esk5_2(X25,X26),k1_relat_1(X26))
        | v5_funct_1(X26,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) )
      & ( ~ r2_hidden(k1_funct_1(X26,esk5_2(X25,X26)),k1_funct_1(X25,esk5_2(X25,X26)))
        | v5_funct_1(X26,X25)
        | ~ v1_relat_1(X26)
        | ~ v1_funct_1(X26)
        | ~ v1_relat_1(X25)
        | ~ v1_funct_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).

fof(c_0_14,negated_conjecture,
    ( v1_relat_1(esk6_0)
    & v1_funct_1(esk6_0)
    & v1_relat_1(esk7_0)
    & v1_funct_1(esk7_0)
    & v5_funct_1(esk7_0,esk6_0)
    & ~ r1_tarski(k1_relat_1(esk7_0),k1_relat_1(esk6_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).

cnf(c_0_15,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( k1_xboole_0 = k1_funct_1(X1,X2)
    | r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X2,X3))
    | ~ v5_funct_1(X1,X2)
    | ~ r2_hidden(X3,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v5_funct_1(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v1_relat_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_relat_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( r2_hidden(X1,k1_relat_1(X2))
    | r2_hidden(X3,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | ~ r2_hidden(X3,k1_funct_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),k1_funct_1(esk6_0,X1))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])])).

fof(c_0_25,plain,(
    ! [X5,X6] :
      ( ~ r2_hidden(X5,X6)
      | ~ r2_hidden(X6,X5) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).

cnf(c_0_26,negated_conjecture,
    ( r2_hidden(k1_funct_1(esk7_0,X1),X2)
    | r2_hidden(X1,k1_relat_1(esk6_0))
    | ~ r2_hidden(X1,k1_relat_1(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_19]),c_0_21])])).

cnf(c_0_27,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),X1)
    | r2_hidden(k1_funct_1(esk7_0,esk1_2(k1_relat_1(esk7_0),X1)),X2)
    | r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_30,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),X1)
    | r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k1_relat_1(esk6_0))
    | ~ r2_hidden(X2,k1_funct_1(esk7_0,esk1_2(k1_relat_1(esk7_0),X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_31,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),X1)
    | r1_tarski(k1_relat_1(esk7_0),X2)
    | r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k1_relat_1(esk6_0))
    | r2_hidden(esk1_2(k1_relat_1(esk7_0),X2),k1_relat_1(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_29])).

cnf(c_0_32,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(k1_relat_1(esk7_0),X1)
    | r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k1_relat_1(esk6_0)) ),
    inference(ef,[status(thm)],[c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( ~ r1_tarski(k1_relat_1(esk7_0),k1_relat_1(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_35,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:42:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.42  # AutoSched0-Mode selected heuristic G_E___207_B07_F1_AE_CS_SP_PI_PS_S0Y
% 0.20/0.42  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.20/0.42  #
% 0.20/0.42  # Preprocessing time       : 0.028 s
% 0.20/0.42  # Presaturation interreduction done
% 0.20/0.42  
% 0.20/0.42  # Proof found!
% 0.20/0.42  # SZS status Theorem
% 0.20/0.42  # SZS output start CNFRefutation
% 0.20/0.42  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.42  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.20/0.42  fof(d4_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:((r2_hidden(X2,k1_relat_1(X1))=>(X3=k1_funct_1(X1,X2)<=>r2_hidden(k4_tarski(X2,X3),X1)))&(~(r2_hidden(X2,k1_relat_1(X1)))=>(X3=k1_funct_1(X1,X2)<=>X3=k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_funct_1)).
% 0.20/0.42  fof(t175_funct_1, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&v5_funct_1(X2,X1))=>r1_tarski(k1_relat_1(X2),k1_relat_1(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_1)).
% 0.20/0.42  fof(d20_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>(v5_funct_1(X2,X1)<=>![X3]:(r2_hidden(X3,k1_relat_1(X2))=>r2_hidden(k1_funct_1(X2,X3),k1_funct_1(X1,X3)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d20_funct_1)).
% 0.20/0.42  fof(antisymmetry_r2_hidden, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 0.20/0.42  fof(c_0_6, plain, ![X7, X8, X9, X10, X11]:((~r1_tarski(X7,X8)|(~r2_hidden(X9,X7)|r2_hidden(X9,X8)))&((r2_hidden(esk1_2(X10,X11),X10)|r1_tarski(X10,X11))&(~r2_hidden(esk1_2(X10,X11),X11)|r1_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.42  fof(c_0_7, plain, ![X13]:r1_tarski(k1_xboole_0,X13), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.20/0.42  fof(c_0_8, plain, ![X29, X30, X31]:(((X31!=k1_funct_1(X29,X30)|r2_hidden(k4_tarski(X30,X31),X29)|~r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(~r2_hidden(k4_tarski(X30,X31),X29)|X31=k1_funct_1(X29,X30)|~r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29))))&((X31!=k1_funct_1(X29,X30)|X31=k1_xboole_0|r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29)))&(X31!=k1_xboole_0|X31=k1_funct_1(X29,X30)|r2_hidden(X30,k1_relat_1(X29))|(~v1_relat_1(X29)|~v1_funct_1(X29))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_funct_1])])])])])).
% 0.20/0.42  fof(c_0_9, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&v5_funct_1(X2,X1))=>r1_tarski(k1_relat_1(X2),k1_relat_1(X1))))), inference(assume_negation,[status(cth)],[t175_funct_1])).
% 0.20/0.42  cnf(c_0_10, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_11, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.42  cnf(c_0_12, plain, (X1=k1_funct_1(X2,X3)|r2_hidden(X3,k1_relat_1(X2))|X1!=k1_xboole_0|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.42  fof(c_0_13, plain, ![X25, X26, X27]:((~v5_funct_1(X26,X25)|(~r2_hidden(X27,k1_relat_1(X26))|r2_hidden(k1_funct_1(X26,X27),k1_funct_1(X25,X27)))|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&((r2_hidden(esk5_2(X25,X26),k1_relat_1(X26))|v5_funct_1(X26,X25)|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25)))&(~r2_hidden(k1_funct_1(X26,esk5_2(X25,X26)),k1_funct_1(X25,esk5_2(X25,X26)))|v5_funct_1(X26,X25)|(~v1_relat_1(X26)|~v1_funct_1(X26))|(~v1_relat_1(X25)|~v1_funct_1(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_funct_1])])])])])).
% 0.20/0.42  fof(c_0_14, negated_conjecture, ((v1_relat_1(esk6_0)&v1_funct_1(esk6_0))&(((v1_relat_1(esk7_0)&v1_funct_1(esk7_0))&v5_funct_1(esk7_0,esk6_0))&~r1_tarski(k1_relat_1(esk7_0),k1_relat_1(esk6_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])).
% 0.20/0.42  cnf(c_0_15, plain, (r2_hidden(X1,X2)|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.42  cnf(c_0_16, plain, (k1_xboole_0=k1_funct_1(X1,X2)|r2_hidden(X2,k1_relat_1(X1))|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[c_0_12])).
% 0.20/0.42  cnf(c_0_17, plain, (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X2,X3))|~v5_funct_1(X1,X2)|~r2_hidden(X3,k1_relat_1(X1))|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.42  cnf(c_0_18, negated_conjecture, (v5_funct_1(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_19, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_20, negated_conjecture, (v1_funct_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_21, negated_conjecture, (v1_relat_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_22, negated_conjecture, (v1_relat_1(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_23, plain, (r2_hidden(X1,k1_relat_1(X2))|r2_hidden(X3,X4)|~v1_funct_1(X2)|~v1_relat_1(X2)|~r2_hidden(X3,k1_funct_1(X2,X1))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.42  cnf(c_0_24, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),k1_funct_1(esk6_0,X1))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])])).
% 0.20/0.42  fof(c_0_25, plain, ![X5, X6]:(~r2_hidden(X5,X6)|~r2_hidden(X6,X5)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[antisymmetry_r2_hidden])])])).
% 0.20/0.42  cnf(c_0_26, negated_conjecture, (r2_hidden(k1_funct_1(esk7_0,X1),X2)|r2_hidden(X1,k1_relat_1(esk6_0))|~r2_hidden(X1,k1_relat_1(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_19]), c_0_21])])).
% 0.20/0.42  cnf(c_0_27, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_28, plain, (~r2_hidden(X1,X2)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.42  cnf(c_0_29, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),X1)|r2_hidden(k1_funct_1(esk7_0,esk1_2(k1_relat_1(esk7_0),X1)),X2)|r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.42  cnf(c_0_30, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),X1)|r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k1_relat_1(esk6_0))|~r2_hidden(X2,k1_funct_1(esk7_0,esk1_2(k1_relat_1(esk7_0),X1)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.42  cnf(c_0_31, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),X1)|r1_tarski(k1_relat_1(esk7_0),X2)|r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k1_relat_1(esk6_0))|r2_hidden(esk1_2(k1_relat_1(esk7_0),X2),k1_relat_1(esk6_0))), inference(spm,[status(thm)],[c_0_30, c_0_29])).
% 0.20/0.42  cnf(c_0_32, plain, (r1_tarski(X1,X2)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.42  cnf(c_0_33, negated_conjecture, (r1_tarski(k1_relat_1(esk7_0),X1)|r2_hidden(esk1_2(k1_relat_1(esk7_0),X1),k1_relat_1(esk6_0))), inference(ef,[status(thm)],[c_0_31])).
% 0.20/0.42  cnf(c_0_34, negated_conjecture, (~r1_tarski(k1_relat_1(esk7_0),k1_relat_1(esk6_0))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.42  cnf(c_0_35, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34]), ['proof']).
% 0.20/0.42  # SZS output end CNFRefutation
% 0.20/0.42  # Proof object total steps             : 36
% 0.20/0.42  # Proof object clause steps            : 23
% 0.20/0.42  # Proof object formula steps           : 13
% 0.20/0.42  # Proof object conjectures             : 16
% 0.20/0.42  # Proof object clause conjectures      : 13
% 0.20/0.42  # Proof object formula conjectures     : 3
% 0.20/0.42  # Proof object initial clauses used    : 13
% 0.20/0.42  # Proof object initial formulas used   : 6
% 0.20/0.42  # Proof object generating inferences   : 10
% 0.20/0.42  # Proof object simplifying inferences  : 9
% 0.20/0.42  # Training examples: 0 positive, 0 negative
% 0.20/0.42  # Parsed axioms                        : 7
% 0.20/0.42  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.42  # Initial clauses                      : 22
% 0.20/0.42  # Removed in clause preprocessing      : 0
% 0.20/0.42  # Initial clauses in saturation        : 22
% 0.20/0.42  # Processed clauses                    : 337
% 0.20/0.42  # ...of these trivial                  : 4
% 0.20/0.42  # ...subsumed                          : 112
% 0.20/0.42  # ...remaining for further processing  : 221
% 0.20/0.42  # Other redundant clauses eliminated   : 0
% 0.20/0.42  # Clauses deleted for lack of memory   : 0
% 0.20/0.42  # Backward-subsumed                    : 25
% 0.20/0.42  # Backward-rewritten                   : 34
% 0.20/0.42  # Generated clauses                    : 1545
% 0.20/0.42  # ...of the previous two non-trivial   : 1467
% 0.20/0.42  # Contextual simplify-reflections      : 1
% 0.20/0.42  # Paramodulations                      : 1472
% 0.20/0.42  # Factorizations                       : 10
% 0.20/0.42  # Equation resolutions                 : 63
% 0.20/0.42  # Propositional unsat checks           : 0
% 0.20/0.42  #    Propositional check models        : 0
% 0.20/0.42  #    Propositional check unsatisfiable : 0
% 0.20/0.42  #    Propositional clauses             : 0
% 0.20/0.42  #    Propositional clauses after purity: 0
% 0.20/0.42  #    Propositional unsat core size     : 0
% 0.20/0.42  #    Propositional preprocessing time  : 0.000
% 0.20/0.42  #    Propositional encoding time       : 0.000
% 0.20/0.42  #    Propositional solver time         : 0.000
% 0.20/0.42  #    Success case prop preproc time    : 0.000
% 0.20/0.42  #    Success case prop encoding time   : 0.000
% 0.20/0.42  #    Success case prop solver time     : 0.000
% 0.20/0.42  # Current number of processed clauses  : 140
% 0.20/0.42  #    Positive orientable unit clauses  : 11
% 0.20/0.42  #    Positive unorientable unit clauses: 0
% 0.20/0.42  #    Negative unit clauses             : 1
% 0.20/0.42  #    Non-unit-clauses                  : 128
% 0.20/0.42  # Current number of unprocessed clauses: 1142
% 0.20/0.42  # ...number of literals in the above   : 6334
% 0.20/0.42  # Current number of archived formulas  : 0
% 0.20/0.42  # Current number of archived clauses   : 81
% 0.20/0.42  # Clause-clause subsumption calls (NU) : 4431
% 0.20/0.42  # Rec. Clause-clause subsumption calls : 2003
% 0.20/0.42  # Non-unit clause-clause subsumptions  : 134
% 0.20/0.42  # Unit Clause-clause subsumption calls : 118
% 0.20/0.42  # Rewrite failures with RHS unbound    : 0
% 0.20/0.42  # BW rewrite match attempts            : 24
% 0.20/0.42  # BW rewrite match successes           : 8
% 0.20/0.42  # Condensation attempts                : 0
% 0.20/0.42  # Condensation successes               : 0
% 0.20/0.42  # Termbank termtop insertions          : 28955
% 0.20/0.42  
% 0.20/0.42  # -------------------------------------------------
% 0.20/0.42  # User time                : 0.074 s
% 0.20/0.42  # System time              : 0.004 s
% 0.20/0.42  # Total time               : 0.078 s
% 0.20/0.42  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
