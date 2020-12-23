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
% DateTime   : Thu Dec  3 10:49:17 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   62 (  73 expanded)
%              Number of clauses        :   32 (  35 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 145 expanded)
%              Number of equality atoms :   36 (  45 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l3_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,k1_tarski(X2))
    <=> ( X1 = k1_xboole_0
        | X1 = k1_tarski(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(t4_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X1,X2)) )
      & ~ ( ? [X3] : r2_hidden(X3,k3_xboole_0(X1,X2))
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(t48_xboole_1,axiom,(
    ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(d6_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(t63_relat_1,conjecture,(
    k3_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_relat_1)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t4_boole,axiom,(
    ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(l27_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ~ r2_hidden(X1,X2)
     => r1_xboole_0(k1_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(rc1_xboole_0,axiom,(
    ? [X1] : v1_xboole_0(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(c_0_15,plain,(
    ! [X22,X23] :
      ( ( ~ r1_tarski(X22,k1_tarski(X23))
        | X22 = k1_xboole_0
        | X22 = k1_tarski(X23) )
      & ( X22 != k1_xboole_0
        | r1_tarski(X22,k1_tarski(X23)) )
      & ( X22 != k1_tarski(X23)
        | r1_tarski(X22,k1_tarski(X23)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).

fof(c_0_16,plain,(
    ! [X6,X7,X9,X10,X11] :
      ( ( r1_xboole_0(X6,X7)
        | r2_hidden(esk2_2(X6,X7),k3_xboole_0(X6,X7)) )
      & ( ~ r2_hidden(X11,k3_xboole_0(X9,X10))
        | ~ r1_xboole_0(X9,X10) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).

fof(c_0_17,plain,(
    ! [X13,X14] : k4_xboole_0(X13,k4_xboole_0(X13,X14)) = k3_xboole_0(X13,X14) ),
    inference(variable_rename,[status(thm)],[t48_xboole_1])).

fof(c_0_18,plain,(
    ! [X38] :
      ( ~ v1_relat_1(X38)
      | k3_relat_1(X38) = k2_xboole_0(k1_relat_1(X38),k2_relat_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).

fof(c_0_19,plain,(
    ! [X30,X31,X34,X36,X37] :
      ( ( ~ v1_relat_1(X30)
        | ~ r2_hidden(X31,X30)
        | X31 = k4_tarski(esk3_2(X30,X31),esk4_2(X30,X31)) )
      & ( r2_hidden(esk5_1(X34),X34)
        | v1_relat_1(X34) )
      & ( esk5_1(X34) != k4_tarski(X36,X37)
        | v1_relat_1(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_20,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(assume_negation,[status(cth)],[t63_relat_1])).

fof(c_0_21,plain,(
    ! [X16,X17,X18] :
      ( ~ r1_tarski(X16,X17)
      | ~ r1_xboole_0(X17,X18)
      | r1_xboole_0(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

cnf(c_0_22,plain,
    ( r1_tarski(X1,k1_tarski(X2))
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( ~ r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k4_xboole_0(X1,k4_xboole_0(X1,X2)) = k3_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X15] : k4_xboole_0(k1_xboole_0,X15) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t4_boole])).

cnf(c_0_26,plain,
    ( k3_relat_1(X1) = k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_27,plain,
    ( r2_hidden(esk5_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X12] : k2_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_29,negated_conjecture,(
    k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(fof_simplification,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,plain,
    ( r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(er,[status(thm)],[c_0_22])).

fof(c_0_32,plain,(
    ! [X20,X21] :
      ( r2_hidden(X20,X21)
      | r1_xboole_0(k1_tarski(X20),X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).

cnf(c_0_33,plain,
    ( ~ r1_xboole_0(X2,X3)
    | ~ r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_34,plain,
    ( k4_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,plain,
    ( k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1)) = k3_relat_1(X1)
    | r2_hidden(esk5_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_37,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_38,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_39,negated_conjecture,
    ( k3_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,plain,
    ( r1_xboole_0(k1_xboole_0,X1)
    | ~ r1_xboole_0(k1_tarski(X2),X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_43,plain,
    ( r2_hidden(esk5_1(k1_xboole_0),k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37]),c_0_38]),c_0_39])).

fof(c_0_44,plain,(
    ! [X28,X29] :
      ( ~ r2_hidden(X28,X29)
      | m1_subset_1(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,X2)
    | r1_xboole_0(k1_xboole_0,X2) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_46,plain,
    ( ~ r1_xboole_0(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

fof(c_0_47,plain,(
    ! [X19] :
      ( ~ v1_xboole_0(X19)
      | X19 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_48,plain,(
    v1_xboole_0(esk1_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).

fof(c_0_49,plain,(
    ! [X24,X25] :
      ( ( ~ m1_subset_1(X25,X24)
        | r2_hidden(X25,X24)
        | v1_xboole_0(X24) )
      & ( ~ r2_hidden(X25,X24)
        | m1_subset_1(X25,X24)
        | v1_xboole_0(X24) )
      & ( ~ m1_subset_1(X25,X24)
        | v1_xboole_0(X25)
        | ~ v1_xboole_0(X24) )
      & ( ~ v1_xboole_0(X25)
        | m1_subset_1(X25,X24)
        | ~ v1_xboole_0(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,plain,
    ( v1_xboole_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_55,plain,
    ( m1_subset_1(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50,c_0_51])])).

cnf(c_0_56,plain,
    ( esk1_0 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_57,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_55])])).

cnf(c_0_58,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(rw,[status(thm)],[c_0_53,c_0_56])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_59])])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39,c_0_60])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 13:59:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.12/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S00AA
% 0.12/0.36  # and selection function SelectLargestOrientable.
% 0.12/0.36  #
% 0.12/0.36  # Preprocessing time       : 0.018 s
% 0.12/0.36  # Presaturation interreduction done
% 0.12/0.36  
% 0.12/0.36  # Proof found!
% 0.12/0.36  # SZS status Theorem
% 0.12/0.36  # SZS output start CNFRefutation
% 0.12/0.36  fof(l3_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(X1,k1_tarski(X2))<=>(X1=k1_xboole_0|X1=k1_tarski(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 0.12/0.36  fof(t4_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~(r2_hidden(X3,k3_xboole_0(X1,X2)))))&~((?[X3]:r2_hidden(X3,k3_xboole_0(X1,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 0.12/0.36  fof(t48_xboole_1, axiom, ![X1, X2]:k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 0.12/0.36  fof(d6_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_relat_1)).
% 0.12/0.36  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.12/0.36  fof(t63_relat_1, conjecture, k3_relat_1(k1_xboole_0)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_relat_1)).
% 0.12/0.36  fof(t63_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_xboole_0(X2,X3))=>r1_xboole_0(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 0.12/0.36  fof(t4_boole, axiom, ![X1]:k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 0.12/0.36  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 0.12/0.36  fof(l27_zfmisc_1, axiom, ![X1, X2]:(~(r2_hidden(X1,X2))=>r1_xboole_0(k1_tarski(X1),X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 0.12/0.36  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 0.12/0.36  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 0.12/0.36  fof(t6_boole, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 0.12/0.36  fof(rc1_xboole_0, axiom, ?[X1]:v1_xboole_0(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 0.12/0.36  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.12/0.36  fof(c_0_15, plain, ![X22, X23]:((~r1_tarski(X22,k1_tarski(X23))|(X22=k1_xboole_0|X22=k1_tarski(X23)))&((X22!=k1_xboole_0|r1_tarski(X22,k1_tarski(X23)))&(X22!=k1_tarski(X23)|r1_tarski(X22,k1_tarski(X23))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_zfmisc_1])])])).
% 0.12/0.36  fof(c_0_16, plain, ![X6, X7, X9, X10, X11]:((r1_xboole_0(X6,X7)|r2_hidden(esk2_2(X6,X7),k3_xboole_0(X6,X7)))&(~r2_hidden(X11,k3_xboole_0(X9,X10))|~r1_xboole_0(X9,X10))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t4_xboole_0])])])])])])).
% 0.12/0.36  fof(c_0_17, plain, ![X13, X14]:k4_xboole_0(X13,k4_xboole_0(X13,X14))=k3_xboole_0(X13,X14), inference(variable_rename,[status(thm)],[t48_xboole_1])).
% 0.12/0.36  fof(c_0_18, plain, ![X38]:(~v1_relat_1(X38)|k3_relat_1(X38)=k2_xboole_0(k1_relat_1(X38),k2_relat_1(X38))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_relat_1])])).
% 0.12/0.36  fof(c_0_19, plain, ![X30, X31, X34, X36, X37]:((~v1_relat_1(X30)|(~r2_hidden(X31,X30)|X31=k4_tarski(esk3_2(X30,X31),esk4_2(X30,X31))))&((r2_hidden(esk5_1(X34),X34)|v1_relat_1(X34))&(esk5_1(X34)!=k4_tarski(X36,X37)|v1_relat_1(X34)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.12/0.36  fof(c_0_20, negated_conjecture, ~(k3_relat_1(k1_xboole_0)=k1_xboole_0), inference(assume_negation,[status(cth)],[t63_relat_1])).
% 0.12/0.36  fof(c_0_21, plain, ![X16, X17, X18]:(~r1_tarski(X16,X17)|~r1_xboole_0(X17,X18)|r1_xboole_0(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).
% 0.12/0.36  cnf(c_0_22, plain, (r1_tarski(X1,k1_tarski(X2))|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.12/0.36  cnf(c_0_23, plain, (~r2_hidden(X1,k3_xboole_0(X2,X3))|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.12/0.36  cnf(c_0_24, plain, (k4_xboole_0(X1,k4_xboole_0(X1,X2))=k3_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.12/0.36  fof(c_0_25, plain, ![X15]:k4_xboole_0(k1_xboole_0,X15)=k1_xboole_0, inference(variable_rename,[status(thm)],[t4_boole])).
% 0.12/0.36  cnf(c_0_26, plain, (k3_relat_1(X1)=k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.12/0.36  cnf(c_0_27, plain, (r2_hidden(esk5_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.12/0.36  fof(c_0_28, plain, ![X12]:k2_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.12/0.36  fof(c_0_29, negated_conjecture, k3_relat_1(k1_xboole_0)!=k1_xboole_0, inference(fof_simplification,[status(thm)],[c_0_20])).
% 0.12/0.36  cnf(c_0_30, plain, (r1_xboole_0(X1,X3)|~r1_tarski(X1,X2)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.12/0.36  cnf(c_0_31, plain, (r1_tarski(k1_xboole_0,k1_tarski(X1))), inference(er,[status(thm)],[c_0_22])).
% 0.12/0.36  fof(c_0_32, plain, ![X20, X21]:(r2_hidden(X20,X21)|r1_xboole_0(k1_tarski(X20),X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l27_zfmisc_1])])])).
% 0.12/0.36  cnf(c_0_33, plain, (~r1_xboole_0(X2,X3)|~r2_hidden(X1,k4_xboole_0(X2,k4_xboole_0(X2,X3)))), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.12/0.36  cnf(c_0_34, plain, (k4_xboole_0(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.36  cnf(c_0_35, plain, (k2_xboole_0(k1_relat_1(X1),k2_relat_1(X1))=k3_relat_1(X1)|r2_hidden(esk5_1(X1),X1)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.12/0.36  cnf(c_0_36, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.12/0.36  cnf(c_0_37, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.12/0.36  cnf(c_0_38, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.12/0.36  cnf(c_0_39, negated_conjecture, (k3_relat_1(k1_xboole_0)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.12/0.36  cnf(c_0_40, plain, (r1_xboole_0(k1_xboole_0,X1)|~r1_xboole_0(k1_tarski(X2),X1)), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.12/0.36  cnf(c_0_41, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.12/0.36  cnf(c_0_42, plain, (~r2_hidden(X1,k1_xboole_0)|~r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.12/0.36  cnf(c_0_43, plain, (r2_hidden(esk5_1(k1_xboole_0),k1_xboole_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_37]), c_0_38]), c_0_39])).
% 0.12/0.36  fof(c_0_44, plain, ![X28, X29]:(~r2_hidden(X28,X29)|m1_subset_1(X28,X29)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.12/0.36  cnf(c_0_45, plain, (r2_hidden(X1,X2)|r1_xboole_0(k1_xboole_0,X2)), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.12/0.36  cnf(c_0_46, plain, (~r1_xboole_0(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.12/0.36  fof(c_0_47, plain, ![X19]:(~v1_xboole_0(X19)|X19=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).
% 0.12/0.36  fof(c_0_48, plain, v1_xboole_0(esk1_0), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[rc1_xboole_0])])).
% 0.12/0.36  fof(c_0_49, plain, ![X24, X25]:(((~m1_subset_1(X25,X24)|r2_hidden(X25,X24)|v1_xboole_0(X24))&(~r2_hidden(X25,X24)|m1_subset_1(X25,X24)|v1_xboole_0(X24)))&((~m1_subset_1(X25,X24)|v1_xboole_0(X25)|~v1_xboole_0(X24))&(~v1_xboole_0(X25)|m1_subset_1(X25,X24)|~v1_xboole_0(X24)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.12/0.36  cnf(c_0_50, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.36  cnf(c_0_51, plain, (r2_hidden(X1,X2)), inference(sr,[status(thm)],[c_0_45, c_0_46])).
% 0.12/0.36  cnf(c_0_52, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.12/0.36  cnf(c_0_53, plain, (v1_xboole_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.36  cnf(c_0_54, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.12/0.36  cnf(c_0_55, plain, (m1_subset_1(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_50, c_0_51])])).
% 0.12/0.36  cnf(c_0_56, plain, (esk1_0=k1_xboole_0), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.12/0.36  cnf(c_0_57, plain, (v1_xboole_0(X1)|~v1_xboole_0(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_55])])).
% 0.12/0.36  cnf(c_0_58, plain, (v1_xboole_0(k1_xboole_0)), inference(rw,[status(thm)],[c_0_53, c_0_56])).
% 0.12/0.36  cnf(c_0_59, plain, (v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_57, c_0_58])).
% 0.12/0.36  cnf(c_0_60, plain, (X1=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_59])])).
% 0.12/0.36  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_39, c_0_60])]), ['proof']).
% 0.12/0.36  # SZS output end CNFRefutation
% 0.12/0.36  # Proof object total steps             : 62
% 0.12/0.36  # Proof object clause steps            : 32
% 0.12/0.36  # Proof object formula steps           : 30
% 0.12/0.36  # Proof object conjectures             : 5
% 0.12/0.36  # Proof object clause conjectures      : 2
% 0.12/0.36  # Proof object formula conjectures     : 3
% 0.12/0.36  # Proof object initial clauses used    : 16
% 0.12/0.36  # Proof object initial formulas used   : 15
% 0.12/0.36  # Proof object generating inferences   : 8
% 0.12/0.36  # Proof object simplifying inferences  : 15
% 0.12/0.36  # Training examples: 0 positive, 0 negative
% 0.12/0.36  # Parsed axioms                        : 16
% 0.12/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.36  # Initial clauses                      : 25
% 0.12/0.36  # Removed in clause preprocessing      : 2
% 0.12/0.36  # Initial clauses in saturation        : 23
% 0.12/0.36  # Processed clauses                    : 69
% 0.12/0.36  # ...of these trivial                  : 1
% 0.12/0.36  # ...subsumed                          : 3
% 0.12/0.36  # ...remaining for further processing  : 65
% 0.12/0.36  # Other redundant clauses eliminated   : 2
% 0.12/0.36  # Clauses deleted for lack of memory   : 0
% 0.12/0.36  # Backward-subsumed                    : 0
% 0.12/0.36  # Backward-rewritten                   : 33
% 0.12/0.36  # Generated clauses                    : 32
% 0.12/0.36  # ...of the previous two non-trivial   : 34
% 0.12/0.36  # Contextual simplify-reflections      : 0
% 0.12/0.36  # Paramodulations                      : 29
% 0.12/0.36  # Factorizations                       : 0
% 0.12/0.36  # Equation resolutions                 : 2
% 0.12/0.36  # Propositional unsat checks           : 0
% 0.12/0.36  #    Propositional check models        : 0
% 0.12/0.36  #    Propositional check unsatisfiable : 0
% 0.12/0.36  #    Propositional clauses             : 0
% 0.12/0.36  #    Propositional clauses after purity: 0
% 0.12/0.36  #    Propositional unsat core size     : 0
% 0.12/0.36  #    Propositional preprocessing time  : 0.000
% 0.12/0.36  #    Propositional encoding time       : 0.000
% 0.12/0.36  #    Propositional solver time         : 0.000
% 0.12/0.36  #    Success case prop preproc time    : 0.000
% 0.12/0.36  #    Success case prop encoding time   : 0.000
% 0.12/0.36  #    Success case prop solver time     : 0.000
% 0.12/0.36  # Current number of processed clauses  : 7
% 0.12/0.36  #    Positive orientable unit clauses  : 3
% 0.12/0.36  #    Positive unorientable unit clauses: 1
% 0.12/0.36  #    Negative unit clauses             : 2
% 0.12/0.36  #    Non-unit-clauses                  : 1
% 0.12/0.36  # Current number of unprocessed clauses: 5
% 0.12/0.36  # ...number of literals in the above   : 9
% 0.12/0.36  # Current number of archived formulas  : 0
% 0.12/0.36  # Current number of archived clauses   : 58
% 0.12/0.36  # Clause-clause subsumption calls (NU) : 8
% 0.12/0.36  # Rec. Clause-clause subsumption calls : 8
% 0.12/0.36  # Non-unit clause-clause subsumptions  : 2
% 0.12/0.36  # Unit Clause-clause subsumption calls : 7
% 0.12/0.36  # Rewrite failures with RHS unbound    : 5
% 0.12/0.36  # BW rewrite match attempts            : 34
% 0.12/0.36  # BW rewrite match successes           : 33
% 0.12/0.36  # Condensation attempts                : 0
% 0.12/0.36  # Condensation successes               : 0
% 0.12/0.36  # Termbank termtop insertions          : 1790
% 0.12/0.36  
% 0.12/0.36  # -------------------------------------------------
% 0.12/0.36  # User time                : 0.021 s
% 0.12/0.36  # System time              : 0.002 s
% 0.12/0.36  # Total time               : 0.023 s
% 0.12/0.36  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
