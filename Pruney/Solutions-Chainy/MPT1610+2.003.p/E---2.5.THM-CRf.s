%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:50 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 213 expanded)
%              Number of clauses        :   35 ( 108 expanded)
%              Number of leaves         :   13 (  52 expanded)
%              Depth                    :   12
%              Number of atoms          :  142 ( 587 expanded)
%              Number of equality atoms :   84 ( 346 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal clause size      :   16 (   1 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_funct_1,axiom,(
    ! [X1,X2] :
      ~ ( ~ ( X1 = k1_xboole_0
            & X2 != k1_xboole_0 )
        & ! [X3] :
            ( ( v1_relat_1(X3)
              & v1_funct_1(X3) )
           => ~ ( X2 = k1_relat_1(X3)
                & r1_tarski(k2_relat_1(X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(t64_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ( ( k1_relat_1(X1) = k1_xboole_0
          | k2_relat_1(X1) = k1_xboole_0 )
       => X1 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(t18_yellow_1,conjecture,(
    ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

fof(d1_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_zfmisc_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> r1_tarski(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(d2_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_yellow_1)).

fof(t4_yellow_1,axiom,(
    ! [X1] : k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

fof(redefinition_k9_setfam_1,axiom,(
    ! [X1] : k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(t13_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k1_xboole_0,X1)
       => k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l13_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(t113_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    <=> ( X1 = k1_xboole_0
        | X2 = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(t203_relat_1,axiom,(
    ! [X1,X2,X3] :
      ( r2_hidden(X1,X2)
     => k11_relat_1(k2_zfmisc_1(X2,X3),X1) = X3 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t203_relat_1)).

fof(c_0_13,plain,(
    ! [X64,X65] :
      ( ( v1_relat_1(esk6_2(X64,X65))
        | X64 = k1_xboole_0 )
      & ( v1_funct_1(esk6_2(X64,X65))
        | X64 = k1_xboole_0 )
      & ( X65 = k1_relat_1(esk6_2(X64,X65))
        | X64 = k1_xboole_0 )
      & ( r1_tarski(k2_relat_1(esk6_2(X64,X65)),X64)
        | X64 = k1_xboole_0 )
      & ( v1_relat_1(esk6_2(X64,X65))
        | X65 != k1_xboole_0 )
      & ( v1_funct_1(esk6_2(X64,X65))
        | X65 != k1_xboole_0 )
      & ( X65 = k1_relat_1(esk6_2(X64,X65))
        | X65 != k1_xboole_0 )
      & ( r1_tarski(k2_relat_1(esk6_2(X64,X65)),X64)
        | X65 != k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_1])])])])).

fof(c_0_14,plain,(
    ! [X63] :
      ( ( k1_relat_1(X63) != k1_xboole_0
        | X63 = k1_xboole_0
        | ~ v1_relat_1(X63) )
      & ( k2_relat_1(X63) != k1_xboole_0
        | X63 = k1_xboole_0
        | ~ v1_relat_1(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).

cnf(c_0_15,plain,
    ( X1 = k1_relat_1(esk6_2(X2,X1))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_16,plain,
    ( v1_relat_1(esk6_2(X1,X2))
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] : k3_yellow_0(k3_yellow_1(X1)) = k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t18_yellow_1])).

fof(c_0_18,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( ( ~ r2_hidden(X43,X42)
        | r1_tarski(X43,X41)
        | X42 != k1_zfmisc_1(X41) )
      & ( ~ r1_tarski(X44,X41)
        | r2_hidden(X44,X42)
        | X42 != k1_zfmisc_1(X41) )
      & ( ~ r2_hidden(esk2_2(X45,X46),X46)
        | ~ r1_tarski(esk2_2(X45,X46),X45)
        | X46 = k1_zfmisc_1(X45) )
      & ( r2_hidden(esk2_2(X45,X46),X46)
        | r1_tarski(esk2_2(X45,X46),X45)
        | X46 = k1_zfmisc_1(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(k2_relat_1(esk6_2(X1,X2)),X1)
    | X2 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( X1 = k1_xboole_0
    | k1_relat_1(X1) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k1_relat_1(esk6_2(X1,k1_xboole_0)) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( v1_relat_1(esk6_2(X1,k1_xboole_0)) ),
    inference(er,[status(thm)],[c_0_16])).

fof(c_0_23,negated_conjecture,(
    k3_yellow_0(k3_yellow_1(esk9_0)) != k1_xboole_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

fof(c_0_24,plain,(
    ! [X75] : k3_yellow_1(X75) = k3_lattice3(k1_lattice3(X75)) ),
    inference(variable_rename,[status(thm)],[d2_yellow_1])).

fof(c_0_25,plain,(
    ! [X77] : k3_yellow_1(X77) = k2_yellow_1(k9_setfam_1(X77)) ),
    inference(variable_rename,[status(thm)],[t4_yellow_1])).

fof(c_0_26,plain,(
    ! [X74] : k9_setfam_1(X74) = k1_zfmisc_1(X74) ),
    inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X3)
    | ~ r1_tarski(X1,X2)
    | X3 != k1_zfmisc_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_28,plain,
    ( r1_tarski(k2_relat_1(esk6_2(X1,k1_xboole_0)),X1) ),
    inference(er,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( esk6_2(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_30,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_31,negated_conjecture,
    ( k3_yellow_0(k3_yellow_1(esk9_0)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( k3_yellow_1(X1) = k3_lattice3(k1_lattice3(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( k3_yellow_1(X1) = k2_yellow_1(k9_setfam_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,plain,
    ( k9_setfam_1(X1) = k1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_35,plain,(
    ! [X76] :
      ( v1_xboole_0(X76)
      | ~ r2_hidden(k1_xboole_0,X76)
      | k3_yellow_0(k2_yellow_1(X76)) = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow_1])])])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_37,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

fof(c_0_38,plain,(
    ! [X14,X15] :
      ( ( r1_tarski(X14,X15)
        | X14 != X15 )
      & ( r1_tarski(X15,X14)
        | X14 != X15 )
      & ( ~ r1_tarski(X14,X15)
        | ~ r1_tarski(X15,X14)
        | X14 = X15 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_39,negated_conjecture,
    ( k3_yellow_0(k3_lattice3(k1_lattice3(esk9_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( k2_yellow_1(k1_zfmisc_1(X1)) = k3_lattice3(k1_lattice3(X1)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33,c_0_34]),c_0_32])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | k3_yellow_0(k2_yellow_1(X1)) = k1_xboole_0
    | ~ r2_hidden(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_42,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_43,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_44,plain,(
    ! [X13] :
      ( ~ v1_xboole_0(X13)
      | X13 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_45,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(k1_zfmisc_1(esk9_0))) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_46,plain,
    ( k3_yellow_0(k2_yellow_1(k1_zfmisc_1(X1))) = k1_xboole_0
    | v1_xboole_0(k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_43])).

cnf(c_0_48,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( v1_xboole_0(k1_zfmisc_1(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

fof(c_0_50,plain,(
    ! [X56,X57] :
      ( ( k2_zfmisc_1(X56,X57) != k1_xboole_0
        | X56 = k1_xboole_0
        | X57 = k1_xboole_0 )
      & ( X56 != k1_xboole_0
        | k2_zfmisc_1(X56,X57) = k1_xboole_0 )
      & ( X57 != k1_xboole_0
        | k2_zfmisc_1(X56,X57) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_51,plain,(
    ! [X58,X59,X60] :
      ( ~ r2_hidden(X58,X59)
      | k11_relat_1(k2_zfmisc_1(X59,X60),X58) = X60 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t203_relat_1])])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( k1_zfmisc_1(esk9_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_54,plain,
    ( k2_zfmisc_1(X1,X2) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_55,plain,
    ( k11_relat_1(k2_zfmisc_1(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk9_0,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( k3_yellow_0(k2_yellow_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(rw,[status(thm)],[c_0_45,c_0_53])).

cnf(c_0_59,negated_conjecture,
    ( k11_relat_1(k1_xboole_0,esk9_0) = X1 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_56]),c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_58,c_0_59]),c_0_59]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:23:42 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.44  # AutoSched0-Mode selected heuristic h208_C18_F1_SE_CS_SP_PS_S002A
% 0.20/0.44  # and selection function SelectNegativeLiterals.
% 0.20/0.44  #
% 0.20/0.44  # Preprocessing time       : 0.029 s
% 0.20/0.44  # Presaturation interreduction done
% 0.20/0.44  
% 0.20/0.44  # Proof found!
% 0.20/0.44  # SZS status Theorem
% 0.20/0.44  # SZS output start CNFRefutation
% 0.20/0.44  fof(t18_funct_1, axiom, ![X1, X2]:~((~((X1=k1_xboole_0&X2!=k1_xboole_0))&![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>~((X2=k1_relat_1(X3)&r1_tarski(k2_relat_1(X3),X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_funct_1)).
% 0.20/0.44  fof(t64_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>((k1_relat_1(X1)=k1_xboole_0|k2_relat_1(X1)=k1_xboole_0)=>X1=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 0.20/0.44  fof(t18_yellow_1, conjecture, ![X1]:k3_yellow_0(k3_yellow_1(X1))=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow_1)).
% 0.20/0.44  fof(d1_zfmisc_1, axiom, ![X1, X2]:(X2=k1_zfmisc_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>r1_tarski(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 0.20/0.44  fof(d2_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_yellow_1)).
% 0.20/0.44  fof(t4_yellow_1, axiom, ![X1]:k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 0.20/0.44  fof(redefinition_k9_setfam_1, axiom, ![X1]:k9_setfam_1(X1)=k1_zfmisc_1(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 0.20/0.44  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.20/0.44  fof(t13_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k1_xboole_0,X1)=>k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 0.20/0.44  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.44  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.20/0.44  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.20/0.44  fof(t203_relat_1, axiom, ![X1, X2, X3]:(r2_hidden(X1,X2)=>k11_relat_1(k2_zfmisc_1(X2,X3),X1)=X3), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t203_relat_1)).
% 0.20/0.44  fof(c_0_13, plain, ![X64, X65]:((((v1_relat_1(esk6_2(X64,X65))|X64=k1_xboole_0)&(v1_funct_1(esk6_2(X64,X65))|X64=k1_xboole_0))&((X65=k1_relat_1(esk6_2(X64,X65))|X64=k1_xboole_0)&(r1_tarski(k2_relat_1(esk6_2(X64,X65)),X64)|X64=k1_xboole_0)))&(((v1_relat_1(esk6_2(X64,X65))|X65!=k1_xboole_0)&(v1_funct_1(esk6_2(X64,X65))|X65!=k1_xboole_0))&((X65=k1_relat_1(esk6_2(X64,X65))|X65!=k1_xboole_0)&(r1_tarski(k2_relat_1(esk6_2(X64,X65)),X64)|X65!=k1_xboole_0)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t18_funct_1])])])])).
% 0.20/0.44  fof(c_0_14, plain, ![X63]:((k1_relat_1(X63)!=k1_xboole_0|X63=k1_xboole_0|~v1_relat_1(X63))&(k2_relat_1(X63)!=k1_xboole_0|X63=k1_xboole_0|~v1_relat_1(X63))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t64_relat_1])])])).
% 0.20/0.44  cnf(c_0_15, plain, (X1=k1_relat_1(esk6_2(X2,X1))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.44  cnf(c_0_16, plain, (v1_relat_1(esk6_2(X1,X2))|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.44  fof(c_0_17, negated_conjecture, ~(![X1]:k3_yellow_0(k3_yellow_1(X1))=k1_xboole_0), inference(assume_negation,[status(cth)],[t18_yellow_1])).
% 0.20/0.44  fof(c_0_18, plain, ![X41, X42, X43, X44, X45, X46]:(((~r2_hidden(X43,X42)|r1_tarski(X43,X41)|X42!=k1_zfmisc_1(X41))&(~r1_tarski(X44,X41)|r2_hidden(X44,X42)|X42!=k1_zfmisc_1(X41)))&((~r2_hidden(esk2_2(X45,X46),X46)|~r1_tarski(esk2_2(X45,X46),X45)|X46=k1_zfmisc_1(X45))&(r2_hidden(esk2_2(X45,X46),X46)|r1_tarski(esk2_2(X45,X46),X45)|X46=k1_zfmisc_1(X45)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_zfmisc_1])])])])])])).
% 0.20/0.44  cnf(c_0_19, plain, (r1_tarski(k2_relat_1(esk6_2(X1,X2)),X1)|X2!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.44  cnf(c_0_20, plain, (X1=k1_xboole_0|k1_relat_1(X1)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.44  cnf(c_0_21, plain, (k1_relat_1(esk6_2(X1,k1_xboole_0))=k1_xboole_0), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.44  cnf(c_0_22, plain, (v1_relat_1(esk6_2(X1,k1_xboole_0))), inference(er,[status(thm)],[c_0_16])).
% 0.20/0.44  fof(c_0_23, negated_conjecture, k3_yellow_0(k3_yellow_1(esk9_0))!=k1_xboole_0, inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.20/0.44  fof(c_0_24, plain, ![X75]:k3_yellow_1(X75)=k3_lattice3(k1_lattice3(X75)), inference(variable_rename,[status(thm)],[d2_yellow_1])).
% 0.20/0.44  fof(c_0_25, plain, ![X77]:k3_yellow_1(X77)=k2_yellow_1(k9_setfam_1(X77)), inference(variable_rename,[status(thm)],[t4_yellow_1])).
% 0.20/0.44  fof(c_0_26, plain, ![X74]:k9_setfam_1(X74)=k1_zfmisc_1(X74), inference(variable_rename,[status(thm)],[redefinition_k9_setfam_1])).
% 0.20/0.44  cnf(c_0_27, plain, (r2_hidden(X1,X3)|~r1_tarski(X1,X2)|X3!=k1_zfmisc_1(X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.44  cnf(c_0_28, plain, (r1_tarski(k2_relat_1(esk6_2(X1,k1_xboole_0)),X1)), inference(er,[status(thm)],[c_0_19])).
% 0.20/0.44  cnf(c_0_29, plain, (esk6_2(X1,k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.20/0.44  cnf(c_0_30, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.20/0.44  cnf(c_0_31, negated_conjecture, (k3_yellow_0(k3_yellow_1(esk9_0))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.44  cnf(c_0_32, plain, (k3_yellow_1(X1)=k3_lattice3(k1_lattice3(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.20/0.44  cnf(c_0_33, plain, (k3_yellow_1(X1)=k2_yellow_1(k9_setfam_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.44  cnf(c_0_34, plain, (k9_setfam_1(X1)=k1_zfmisc_1(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.44  fof(c_0_35, plain, ![X76]:(v1_xboole_0(X76)|(~r2_hidden(k1_xboole_0,X76)|k3_yellow_0(k2_yellow_1(X76))=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t13_yellow_1])])])).
% 0.20/0.44  cnf(c_0_36, plain, (r2_hidden(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.44  cnf(c_0_37, plain, (r1_tarski(k1_xboole_0,X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_28, c_0_29]), c_0_30])).
% 0.20/0.44  fof(c_0_38, plain, ![X14, X15]:(((r1_tarski(X14,X15)|X14!=X15)&(r1_tarski(X15,X14)|X14!=X15))&(~r1_tarski(X14,X15)|~r1_tarski(X15,X14)|X14=X15)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.44  cnf(c_0_39, negated_conjecture, (k3_yellow_0(k3_lattice3(k1_lattice3(esk9_0)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.44  cnf(c_0_40, plain, (k2_yellow_1(k1_zfmisc_1(X1))=k3_lattice3(k1_lattice3(X1))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_33, c_0_34]), c_0_32])).
% 0.20/0.44  cnf(c_0_41, plain, (v1_xboole_0(X1)|k3_yellow_0(k2_yellow_1(X1))=k1_xboole_0|~r2_hidden(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.20/0.44  cnf(c_0_42, plain, (r2_hidden(k1_xboole_0,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.44  cnf(c_0_43, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.44  fof(c_0_44, plain, ![X13]:(~v1_xboole_0(X13)|X13=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.20/0.44  cnf(c_0_45, negated_conjecture, (k3_yellow_0(k2_yellow_1(k1_zfmisc_1(esk9_0)))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.44  cnf(c_0_46, plain, (k3_yellow_0(k2_yellow_1(k1_zfmisc_1(X1)))=k1_xboole_0|v1_xboole_0(k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.44  cnf(c_0_47, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_43])).
% 0.20/0.44  cnf(c_0_48, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.44  cnf(c_0_49, negated_conjecture, (v1_xboole_0(k1_zfmisc_1(esk9_0))), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.44  fof(c_0_50, plain, ![X56, X57]:((k2_zfmisc_1(X56,X57)!=k1_xboole_0|(X56=k1_xboole_0|X57=k1_xboole_0))&((X56!=k1_xboole_0|k2_zfmisc_1(X56,X57)=k1_xboole_0)&(X57!=k1_xboole_0|k2_zfmisc_1(X56,X57)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.20/0.44  fof(c_0_51, plain, ![X58, X59, X60]:(~r2_hidden(X58,X59)|k11_relat_1(k2_zfmisc_1(X59,X60),X58)=X60), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t203_relat_1])])).
% 0.20/0.44  cnf(c_0_52, plain, (r2_hidden(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_36, c_0_47])).
% 0.20/0.44  cnf(c_0_53, negated_conjecture, (k1_zfmisc_1(esk9_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.20/0.44  cnf(c_0_54, plain, (k2_zfmisc_1(X1,X2)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.44  cnf(c_0_55, plain, (k11_relat_1(k2_zfmisc_1(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.44  cnf(c_0_56, negated_conjecture, (r2_hidden(esk9_0,k1_xboole_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.44  cnf(c_0_57, plain, (k2_zfmisc_1(k1_xboole_0,X1)=k1_xboole_0), inference(er,[status(thm)],[c_0_54])).
% 0.20/0.44  cnf(c_0_58, negated_conjecture, (k3_yellow_0(k2_yellow_1(k1_xboole_0))!=k1_xboole_0), inference(rw,[status(thm)],[c_0_45, c_0_53])).
% 0.20/0.44  cnf(c_0_59, negated_conjecture, (k11_relat_1(k1_xboole_0,esk9_0)=X1), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_56]), c_0_57])).
% 0.20/0.44  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_58, c_0_59]), c_0_59]), ['proof']).
% 0.20/0.44  # SZS output end CNFRefutation
% 0.20/0.44  # Proof object total steps             : 61
% 0.20/0.44  # Proof object clause steps            : 35
% 0.20/0.44  # Proof object formula steps           : 26
% 0.20/0.44  # Proof object conjectures             : 12
% 0.20/0.44  # Proof object clause conjectures      : 9
% 0.20/0.44  # Proof object formula conjectures     : 3
% 0.20/0.44  # Proof object initial clauses used    : 15
% 0.20/0.44  # Proof object initial formulas used   : 13
% 0.20/0.44  # Proof object generating inferences   : 8
% 0.20/0.44  # Proof object simplifying inferences  : 18
% 0.20/0.44  # Training examples: 0 positive, 0 negative
% 0.20/0.44  # Parsed axioms                        : 18
% 0.20/0.44  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.44  # Initial clauses                      : 65
% 0.20/0.44  # Removed in clause preprocessing      : 2
% 0.20/0.44  # Initial clauses in saturation        : 63
% 0.20/0.44  # Processed clauses                    : 356
% 0.20/0.44  # ...of these trivial                  : 1
% 0.20/0.44  # ...subsumed                          : 58
% 0.20/0.44  # ...remaining for further processing  : 297
% 0.20/0.44  # Other redundant clauses eliminated   : 280
% 0.20/0.44  # Clauses deleted for lack of memory   : 0
% 0.20/0.44  # Backward-subsumed                    : 13
% 0.20/0.44  # Backward-rewritten                   : 140
% 0.20/0.44  # Generated clauses                    : 4921
% 0.20/0.44  # ...of the previous two non-trivial   : 4392
% 0.20/0.44  # Contextual simplify-reflections      : 0
% 0.20/0.44  # Paramodulations                      : 4651
% 0.20/0.44  # Factorizations                       : 0
% 0.20/0.44  # Equation resolutions                 : 280
% 0.20/0.44  # Propositional unsat checks           : 0
% 0.20/0.44  #    Propositional check models        : 0
% 0.20/0.44  #    Propositional check unsatisfiable : 0
% 0.20/0.44  #    Propositional clauses             : 0
% 0.20/0.44  #    Propositional clauses after purity: 0
% 0.20/0.44  #    Propositional unsat core size     : 0
% 0.20/0.44  #    Propositional preprocessing time  : 0.000
% 0.20/0.44  #    Propositional encoding time       : 0.000
% 0.20/0.44  #    Propositional solver time         : 0.000
% 0.20/0.44  #    Success case prop preproc time    : 0.000
% 0.20/0.44  #    Success case prop encoding time   : 0.000
% 0.20/0.44  #    Success case prop solver time     : 0.000
% 0.20/0.44  # Current number of processed clauses  : 60
% 0.20/0.44  #    Positive orientable unit clauses  : 18
% 0.20/0.44  #    Positive unorientable unit clauses: 1
% 0.20/0.44  #    Negative unit clauses             : 0
% 0.20/0.44  #    Non-unit-clauses                  : 41
% 0.20/0.44  # Current number of unprocessed clauses: 4136
% 0.20/0.44  # ...number of literals in the above   : 12005
% 0.20/0.44  # Current number of archived formulas  : 0
% 0.20/0.44  # Current number of archived clauses   : 217
% 0.20/0.44  # Clause-clause subsumption calls (NU) : 3558
% 0.20/0.44  # Rec. Clause-clause subsumption calls : 2940
% 0.20/0.44  # Non-unit clause-clause subsumptions  : 59
% 0.20/0.44  # Unit Clause-clause subsumption calls : 472
% 0.20/0.44  # Rewrite failures with RHS unbound    : 2
% 0.20/0.44  # BW rewrite match attempts            : 205
% 0.20/0.44  # BW rewrite match successes           : 110
% 0.20/0.44  # Condensation attempts                : 0
% 0.20/0.44  # Condensation successes               : 0
% 0.20/0.44  # Termbank termtop insertions          : 58618
% 0.20/0.44  
% 0.20/0.44  # -------------------------------------------------
% 0.20/0.44  # User time                : 0.098 s
% 0.20/0.44  # System time              : 0.007 s
% 0.20/0.44  # Total time               : 0.105 s
% 0.20/0.44  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
