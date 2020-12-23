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
% DateTime   : Thu Dec  3 11:07:26 EST 2020

% Result     : Theorem 0.87s
% Output     : CNFRefutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of clauses        :   17 (  18 expanded)
%              Number of leaves         :    7 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   78 ( 125 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal clause size      :    7 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t19_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X1,X3) )
     => r1_tarski(X1,k3_xboole_0(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(t175_funct_2,conjecture,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2,X3] :
          ( r1_tarski(k10_relat_1(X1,X3),X2)
         => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

fof(t139_funct_1,axiom,(
    ! [X1,X2,X3] :
      ( v1_relat_1(X3)
     => k10_relat_1(k7_relat_1(X3,X1),X2) = k3_xboole_0(X1,k10_relat_1(X3,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

fof(t179_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( r1_tarski(X2,X3)
           => r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t179_relat_1)).

fof(t88_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k7_relat_1(X2,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(dt_k7_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X1)
     => v1_relat_1(k7_relat_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(c_0_7,plain,(
    ! [X17,X18] :
      ( ( r1_tarski(X17,X18)
        | X17 != X18 )
      & ( r1_tarski(X18,X17)
        | X17 != X18 )
      & ( ~ r1_tarski(X17,X18)
        | ~ r1_tarski(X18,X17)
        | X17 = X18 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_8,plain,(
    ! [X30,X31,X32] :
      ( ~ r1_tarski(X30,X31)
      | ~ r1_tarski(X30,X32)
      | r1_tarski(X30,k3_xboole_0(X31,X32)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).

cnf(c_0_9,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( v1_relat_1(X1)
          & v1_funct_1(X1) )
       => ! [X2,X3] :
            ( r1_tarski(k10_relat_1(X1,X3),X2)
           => k10_relat_1(X1,X3) = k10_relat_1(k7_relat_1(X1,X2),X3) ) ) ),
    inference(assume_negation,[status(cth)],[t175_funct_2])).

cnf(c_0_11,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X3))
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_9])).

fof(c_0_13,negated_conjecture,
    ( v1_relat_1(esk39_0)
    & v1_funct_1(esk39_0)
    & r1_tarski(k10_relat_1(esk39_0,esk41_0),esk40_0)
    & k10_relat_1(esk39_0,esk41_0) != k10_relat_1(k7_relat_1(esk39_0,esk40_0),esk41_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).

cnf(c_0_14,plain,
    ( r1_tarski(X1,k3_xboole_0(X2,X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_11,c_0_12])).

cnf(c_0_15,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk39_0,esk41_0),esk40_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_16,plain,(
    ! [X223,X224,X225] :
      ( ~ v1_relat_1(X225)
      | k10_relat_1(k7_relat_1(X225,X223),X224) = k3_xboole_0(X223,k10_relat_1(X225,X224)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk39_0,esk41_0),k3_xboole_0(esk40_0,k10_relat_1(esk39_0,esk41_0))) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_18,plain,
    ( k10_relat_1(k7_relat_1(X1,X2),X3) = k3_xboole_0(X2,k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_19,negated_conjecture,
    ( v1_relat_1(esk39_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X134,X135,X136] :
      ( ~ v1_relat_1(X135)
      | ~ v1_relat_1(X136)
      | ~ r1_tarski(X135,X136)
      | r1_tarski(k10_relat_1(X135,X134),k10_relat_1(X136,X134)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t179_relat_1])])])).

fof(c_0_21,plain,(
    ! [X166,X167] :
      ( ~ v1_relat_1(X167)
      | r1_tarski(k7_relat_1(X167,X166),X167) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).

fof(c_0_22,plain,(
    ! [X76,X77] :
      ( ~ v1_relat_1(X76)
      | v1_relat_1(k7_relat_1(X76,X77)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).

cnf(c_0_23,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( r1_tarski(k10_relat_1(esk39_0,esk41_0),k10_relat_1(k7_relat_1(esk39_0,esk40_0),esk41_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_25,negated_conjecture,
    ( k10_relat_1(esk39_0,esk41_0) != k10_relat_1(k7_relat_1(esk39_0,esk40_0),esk41_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_26,plain,
    ( r1_tarski(k10_relat_1(X1,X3),k10_relat_1(X2,X3))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( r1_tarski(k7_relat_1(X1,X2),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( v1_relat_1(k7_relat_1(X1,X2))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tarski(k10_relat_1(k7_relat_1(esk39_0,esk40_0),esk41_0),k10_relat_1(esk39_0,esk41_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25])).

cnf(c_0_30,plain,
    ( r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),k10_relat_1(X1,X3))
    | ~ v1_relat_1(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

cnf(c_0_31,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:58:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.87/1.04  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S5PRR_S4d
% 0.87/1.04  # and selection function SelectCQIPrecWNTNp.
% 0.87/1.04  #
% 0.87/1.04  # Preprocessing time       : 0.037 s
% 0.87/1.04  # Presaturation interreduction done
% 0.87/1.04  
% 0.87/1.04  # Proof found!
% 0.87/1.04  # SZS status Theorem
% 0.87/1.04  # SZS output start CNFRefutation
% 0.87/1.04  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.87/1.04  fof(t19_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X1,X3))=>r1_tarski(X1,k3_xboole_0(X2,X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 0.87/1.04  fof(t175_funct_2, conjecture, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 0.87/1.04  fof(t139_funct_1, axiom, ![X1, X2, X3]:(v1_relat_1(X3)=>k10_relat_1(k7_relat_1(X3,X1),X2)=k3_xboole_0(X1,k10_relat_1(X3,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 0.87/1.04  fof(t179_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>![X3]:(v1_relat_1(X3)=>(r1_tarski(X2,X3)=>r1_tarski(k10_relat_1(X2,X1),k10_relat_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t179_relat_1)).
% 0.87/1.04  fof(t88_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>r1_tarski(k7_relat_1(X2,X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 0.87/1.04  fof(dt_k7_relat_1, axiom, ![X1, X2]:(v1_relat_1(X1)=>v1_relat_1(k7_relat_1(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 0.87/1.04  fof(c_0_7, plain, ![X17, X18]:(((r1_tarski(X17,X18)|X17!=X18)&(r1_tarski(X18,X17)|X17!=X18))&(~r1_tarski(X17,X18)|~r1_tarski(X18,X17)|X17=X18)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.87/1.04  fof(c_0_8, plain, ![X30, X31, X32]:(~r1_tarski(X30,X31)|~r1_tarski(X30,X32)|r1_tarski(X30,k3_xboole_0(X31,X32))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t19_xboole_1])])).
% 0.87/1.04  cnf(c_0_9, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.87/1.04  fof(c_0_10, negated_conjecture, ~(![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2, X3]:(r1_tarski(k10_relat_1(X1,X3),X2)=>k10_relat_1(X1,X3)=k10_relat_1(k7_relat_1(X1,X2),X3)))), inference(assume_negation,[status(cth)],[t175_funct_2])).
% 0.87/1.04  cnf(c_0_11, plain, (r1_tarski(X1,k3_xboole_0(X2,X3))|~r1_tarski(X1,X2)|~r1_tarski(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.87/1.04  cnf(c_0_12, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_9])).
% 0.87/1.04  fof(c_0_13, negated_conjecture, ((v1_relat_1(esk39_0)&v1_funct_1(esk39_0))&(r1_tarski(k10_relat_1(esk39_0,esk41_0),esk40_0)&k10_relat_1(esk39_0,esk41_0)!=k10_relat_1(k7_relat_1(esk39_0,esk40_0),esk41_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_10])])])).
% 0.87/1.04  cnf(c_0_14, plain, (r1_tarski(X1,k3_xboole_0(X2,X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_11, c_0_12])).
% 0.87/1.04  cnf(c_0_15, negated_conjecture, (r1_tarski(k10_relat_1(esk39_0,esk41_0),esk40_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.87/1.04  fof(c_0_16, plain, ![X223, X224, X225]:(~v1_relat_1(X225)|k10_relat_1(k7_relat_1(X225,X223),X224)=k3_xboole_0(X223,k10_relat_1(X225,X224))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t139_funct_1])])).
% 0.87/1.04  cnf(c_0_17, negated_conjecture, (r1_tarski(k10_relat_1(esk39_0,esk41_0),k3_xboole_0(esk40_0,k10_relat_1(esk39_0,esk41_0)))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.87/1.04  cnf(c_0_18, plain, (k10_relat_1(k7_relat_1(X1,X2),X3)=k3_xboole_0(X2,k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.87/1.04  cnf(c_0_19, negated_conjecture, (v1_relat_1(esk39_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.87/1.04  fof(c_0_20, plain, ![X134, X135, X136]:(~v1_relat_1(X135)|(~v1_relat_1(X136)|(~r1_tarski(X135,X136)|r1_tarski(k10_relat_1(X135,X134),k10_relat_1(X136,X134))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t179_relat_1])])])).
% 0.87/1.04  fof(c_0_21, plain, ![X166, X167]:(~v1_relat_1(X167)|r1_tarski(k7_relat_1(X167,X166),X167)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t88_relat_1])])).
% 0.87/1.04  fof(c_0_22, plain, ![X76, X77]:(~v1_relat_1(X76)|v1_relat_1(k7_relat_1(X76,X77))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k7_relat_1])])).
% 0.87/1.04  cnf(c_0_23, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.87/1.04  cnf(c_0_24, negated_conjecture, (r1_tarski(k10_relat_1(esk39_0,esk41_0),k10_relat_1(k7_relat_1(esk39_0,esk40_0),esk41_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19])])).
% 0.87/1.04  cnf(c_0_25, negated_conjecture, (k10_relat_1(esk39_0,esk41_0)!=k10_relat_1(k7_relat_1(esk39_0,esk40_0),esk41_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.87/1.04  cnf(c_0_26, plain, (r1_tarski(k10_relat_1(X1,X3),k10_relat_1(X2,X3))|~v1_relat_1(X1)|~v1_relat_1(X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.87/1.04  cnf(c_0_27, plain, (r1_tarski(k7_relat_1(X1,X2),X1)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.87/1.04  cnf(c_0_28, plain, (v1_relat_1(k7_relat_1(X1,X2))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.87/1.04  cnf(c_0_29, negated_conjecture, (~r1_tarski(k10_relat_1(k7_relat_1(esk39_0,esk40_0),esk41_0),k10_relat_1(esk39_0,esk41_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25])).
% 0.87/1.04  cnf(c_0_30, plain, (r1_tarski(k10_relat_1(k7_relat_1(X1,X2),X3),k10_relat_1(X1,X3))|~v1_relat_1(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28])).
% 0.87/1.04  cnf(c_0_31, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_19])]), ['proof']).
% 0.87/1.04  # SZS output end CNFRefutation
% 0.87/1.04  # Proof object total steps             : 32
% 0.87/1.04  # Proof object clause steps            : 17
% 0.87/1.04  # Proof object formula steps           : 15
% 0.87/1.04  # Proof object conjectures             : 10
% 0.87/1.04  # Proof object clause conjectures      : 7
% 0.87/1.04  # Proof object formula conjectures     : 3
% 0.87/1.04  # Proof object initial clauses used    : 10
% 0.87/1.04  # Proof object initial formulas used   : 7
% 0.87/1.04  # Proof object generating inferences   : 6
% 0.87/1.04  # Proof object simplifying inferences  : 7
% 0.87/1.04  # Training examples: 0 positive, 0 negative
% 0.87/1.04  # Parsed axioms                        : 107
% 0.87/1.04  # Removed by relevancy pruning/SinE    : 0
% 0.87/1.04  # Initial clauses                      : 213
% 0.87/1.04  # Removed in clause preprocessing      : 2
% 0.87/1.04  # Initial clauses in saturation        : 211
% 0.87/1.04  # Processed clauses                    : 7849
% 0.87/1.04  # ...of these trivial                  : 65
% 0.87/1.04  # ...subsumed                          : 5055
% 0.87/1.04  # ...remaining for further processing  : 2729
% 0.87/1.04  # Other redundant clauses eliminated   : 44
% 0.87/1.04  # Clauses deleted for lack of memory   : 0
% 0.87/1.04  # Backward-subsumed                    : 20
% 0.87/1.04  # Backward-rewritten                   : 343
% 0.87/1.04  # Generated clauses                    : 45733
% 0.87/1.04  # ...of the previous two non-trivial   : 38762
% 0.87/1.04  # Contextual simplify-reflections      : 65
% 0.87/1.04  # Paramodulations                      : 45675
% 0.87/1.04  # Factorizations                       : 13
% 0.87/1.04  # Equation resolutions                 : 46
% 0.87/1.04  # Propositional unsat checks           : 0
% 0.87/1.04  #    Propositional check models        : 0
% 0.87/1.04  #    Propositional check unsatisfiable : 0
% 0.87/1.04  #    Propositional clauses             : 0
% 0.87/1.04  #    Propositional clauses after purity: 0
% 0.87/1.04  #    Propositional unsat core size     : 0
% 0.87/1.04  #    Propositional preprocessing time  : 0.000
% 0.87/1.04  #    Propositional encoding time       : 0.000
% 0.87/1.04  #    Propositional solver time         : 0.000
% 0.87/1.04  #    Success case prop preproc time    : 0.000
% 0.87/1.04  #    Success case prop encoding time   : 0.000
% 0.87/1.04  #    Success case prop solver time     : 0.000
% 0.87/1.04  # Current number of processed clauses  : 2145
% 0.87/1.04  #    Positive orientable unit clauses  : 512
% 0.87/1.04  #    Positive unorientable unit clauses: 0
% 0.87/1.04  #    Negative unit clauses             : 421
% 0.87/1.04  #    Non-unit-clauses                  : 1212
% 0.87/1.04  # Current number of unprocessed clauses: 30850
% 0.87/1.04  # ...number of literals in the above   : 70109
% 0.87/1.04  # Current number of archived formulas  : 0
% 0.87/1.04  # Current number of archived clauses   : 564
% 0.87/1.04  # Clause-clause subsumption calls (NU) : 128930
% 0.87/1.04  # Rec. Clause-clause subsumption calls : 88277
% 0.87/1.04  # Non-unit clause-clause subsumptions  : 988
% 0.87/1.04  # Unit Clause-clause subsumption calls : 176422
% 0.87/1.04  # Rewrite failures with RHS unbound    : 0
% 0.87/1.04  # BW rewrite match attempts            : 1475
% 0.87/1.04  # BW rewrite match successes           : 132
% 0.87/1.04  # Condensation attempts                : 0
% 0.87/1.04  # Condensation successes               : 0
% 0.87/1.04  # Termbank termtop insertions          : 816712
% 0.87/1.04  
% 0.87/1.04  # -------------------------------------------------
% 0.87/1.04  # User time                : 0.668 s
% 0.87/1.04  # System time              : 0.027 s
% 0.87/1.04  # Total time               : 0.695 s
% 0.87/1.04  # Maximum resident set size: 1716 pages
%------------------------------------------------------------------------------
