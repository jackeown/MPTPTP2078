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
% DateTime   : Thu Dec  3 10:53:00 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 358 expanded)
%              Number of clauses        :   44 ( 163 expanded)
%              Number of leaves         :    8 (  95 expanded)
%              Depth                    :   12
%              Number of atoms          :  171 (1203 expanded)
%              Number of equality atoms :   69 ( 506 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t95_relat_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( k7_relat_1(X2,X1) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(t98_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,k1_relat_1(X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(t66_xboole_1,axiom,(
    ! [X1] :
      ( ~ ( ~ r1_xboole_0(X1,X1)
          & X1 = k1_xboole_0 )
      & ~ ( X1 != k1_xboole_0
          & r1_xboole_0(X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(s3_funct_1__e2_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(t16_funct_1,conjecture,(
    ! [X1] :
      ( ! [X2] :
          ( ( v1_relat_1(X2)
            & v1_funct_1(X2) )
         => ! [X3] :
              ( ( v1_relat_1(X3)
                & v1_funct_1(X3) )
             => ( ( k1_relat_1(X2) = X1
                  & k1_relat_1(X3) = X1 )
               => X2 = X3 ) ) )
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(d4_relat_1,axiom,(
    ! [X1,X2] :
      ( X2 = k1_relat_1(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4] : r2_hidden(k4_tarski(X3,X4),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(c_0_8,plain,(
    ! [X24,X25] :
      ( ( k7_relat_1(X25,X24) != k1_xboole_0
        | r1_xboole_0(k1_relat_1(X25),X24)
        | ~ v1_relat_1(X25) )
      & ( ~ r1_xboole_0(k1_relat_1(X25),X24)
        | k7_relat_1(X25,X24) = k1_xboole_0
        | ~ v1_relat_1(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).

fof(c_0_9,plain,(
    ! [X27,X28,X30] :
      ( v1_relat_1(esk7_2(X27,X28))
      & v1_funct_1(esk7_2(X27,X28))
      & k1_relat_1(esk7_2(X27,X28)) = X27
      & ( ~ r2_hidden(X30,X27)
        | k1_funct_1(esk7_2(X27,X28),X30) = X28 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

fof(c_0_10,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k7_relat_1(X26,k1_relat_1(X26)) = X26 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).

cnf(c_0_11,plain,
    ( k7_relat_1(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_12,plain,
    ( k1_relat_1(esk7_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( v1_relat_1(esk7_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_14,plain,(
    ! [X9] :
      ( ( r1_xboole_0(X9,X9)
        | X9 != k1_xboole_0 )
      & ( X9 = k1_xboole_0
        | ~ r1_xboole_0(X9,X9) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).

cnf(c_0_15,plain,
    ( k7_relat_1(X1,k1_relat_1(X1)) = X1
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k7_relat_1(esk7_2(X1,X2),X3) = k1_xboole_0
    | ~ r1_xboole_0(X1,X3) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_17,plain,
    ( r1_xboole_0(X1,X1)
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_18,plain,(
    ! [X31,X33] :
      ( v1_relat_1(esk8_1(X31))
      & v1_funct_1(esk8_1(X31))
      & k1_relat_1(esk8_1(X31)) = X31
      & ( ~ r2_hidden(X33,X31)
        | k1_funct_1(esk8_1(X31),X33) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ! [X2] :
            ( ( v1_relat_1(X2)
              & v1_funct_1(X2) )
           => ! [X3] :
                ( ( v1_relat_1(X3)
                  & v1_funct_1(X3) )
               => ( ( k1_relat_1(X2) = X1
                    & k1_relat_1(X3) = X1 )
                 => X2 = X3 ) ) )
       => X1 = k1_xboole_0 ) ),
    inference(assume_negation,[status(cth)],[t16_funct_1])).

fof(c_0_20,plain,(
    ! [X10,X11,X12,X14,X15,X16,X17,X19] :
      ( ( ~ r2_hidden(X12,X11)
        | r2_hidden(k4_tarski(X12,esk2_3(X10,X11,X12)),X10)
        | X11 != k1_relat_1(X10) )
      & ( ~ r2_hidden(k4_tarski(X14,X15),X10)
        | r2_hidden(X14,X11)
        | X11 != k1_relat_1(X10) )
      & ( ~ r2_hidden(esk3_2(X16,X17),X17)
        | ~ r2_hidden(k4_tarski(esk3_2(X16,X17),X19),X16)
        | X17 = k1_relat_1(X16) )
      & ( r2_hidden(esk3_2(X16,X17),X17)
        | r2_hidden(k4_tarski(esk3_2(X16,X17),esk4_2(X16,X17)),X16)
        | X17 = k1_relat_1(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).

cnf(c_0_21,plain,
    ( esk7_2(X1,X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_13]),c_0_12])])).

cnf(c_0_22,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(er,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( k1_relat_1(esk8_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( v1_relat_1(esk8_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,negated_conjecture,(
    ! [X35,X36] :
      ( ( ~ v1_relat_1(X35)
        | ~ v1_funct_1(X35)
        | ~ v1_relat_1(X36)
        | ~ v1_funct_1(X36)
        | k1_relat_1(X35) != esk9_0
        | k1_relat_1(X36) != esk9_0
        | X35 = X36 )
      & esk9_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).

fof(c_0_26,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_27,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)
    | ~ r2_hidden(X1,X2)
    | X2 != k1_relat_1(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k1_funct_1(esk7_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,plain,
    ( esk7_2(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_30,plain,
    ( k7_relat_1(esk8_1(X1),X2) = k1_xboole_0
    | ~ r1_xboole_0(X1,X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_23]),c_0_24])])).

cnf(c_0_31,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk9_0
    | k1_relat_1(X2) != esk9_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( v1_funct_1(esk8_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_34,plain,
    ( r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)
    | ~ r2_hidden(X1,k1_relat_1(X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_35,plain,
    ( k1_funct_1(k1_xboole_0,X1) = X2
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( X1 = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_37,plain,
    ( r1_xboole_0(k1_relat_1(X1),X2)
    | k7_relat_1(X1,X2) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_38,plain,
    ( esk8_1(X1) = k1_xboole_0
    | ~ r1_xboole_0(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_30]),c_0_24]),c_0_23])])).

cnf(c_0_39,negated_conjecture,
    ( X1 = esk8_1(esk9_0)
    | k1_relat_1(X1) != esk9_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_23]),c_0_32]),c_0_24])])])).

cnf(c_0_40,plain,
    ( v1_funct_1(esk7_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_41,plain,
    ( ~ r2_hidden(X1,k1_relat_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_42,plain,
    ( X1 = X2
    | ~ r2_hidden(X3,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_35,c_0_35])).

cnf(c_0_43,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,plain,
    ( k1_relat_1(X1) = k1_xboole_0
    | k7_relat_1(X1,k1_relat_1(X1)) != k1_xboole_0
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_45,plain,
    ( esk8_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_38,c_0_22])).

cnf(c_0_46,negated_conjecture,
    ( esk7_2(esk9_0,X1) = esk8_1(esk9_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_12]),c_0_40]),c_0_13])])])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_relat_1(k1_relat_1(X2)))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_41,c_0_34])).

cnf(c_0_48,plain,
    ( r2_hidden(esk3_2(X1,X2),X2)
    | r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)
    | X2 = k1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( esk9_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_50,plain,
    ( X1 = X2
    | v1_xboole_0(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_15])])).

cnf(c_0_52,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_45])).

cnf(c_0_53,negated_conjecture,
    ( k1_funct_1(esk8_1(esk9_0),X1) = X2
    | ~ r2_hidden(X1,esk9_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_46])).

cnf(c_0_54,plain,
    ( X1 = k1_relat_1(k1_relat_1(k1_relat_1(X2)))
    | r2_hidden(esk3_2(k1_relat_1(k1_relat_1(X2)),X1),X1)
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50])])).

cnf(c_0_56,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51,c_0_52])])).

cnf(c_0_57,negated_conjecture,
    ( X1 = X2
    | ~ r2_hidden(X3,esk9_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( X1 = k1_xboole_0
    | r2_hidden(esk3_2(k1_xboole_0,X1),X1) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56]),c_0_56]),c_0_56]),c_0_56]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( X1 = X2 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[c_0_49,c_0_59]),
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.45  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.45  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.45  #
% 0.20/0.45  # Preprocessing time       : 0.028 s
% 0.20/0.45  # Presaturation interreduction done
% 0.20/0.45  
% 0.20/0.45  # Proof found!
% 0.20/0.45  # SZS status Theorem
% 0.20/0.45  # SZS output start CNFRefutation
% 0.20/0.45  fof(t95_relat_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(k7_relat_1(X2,X1)=k1_xboole_0<=>r1_xboole_0(k1_relat_1(X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 0.20/0.45  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.20/0.45  fof(t98_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>k7_relat_1(X1,k1_relat_1(X1))=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 0.20/0.45  fof(t66_xboole_1, axiom, ![X1]:(~((~(r1_xboole_0(X1,X1))&X1=k1_xboole_0))&~((X1!=k1_xboole_0&r1_xboole_0(X1,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 0.20/0.45  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.20/0.45  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 0.20/0.45  fof(d4_relat_1, axiom, ![X1, X2]:(X2=k1_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:r2_hidden(k4_tarski(X3,X4),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_relat_1)).
% 0.20/0.45  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.45  fof(c_0_8, plain, ![X24, X25]:((k7_relat_1(X25,X24)!=k1_xboole_0|r1_xboole_0(k1_relat_1(X25),X24)|~v1_relat_1(X25))&(~r1_xboole_0(k1_relat_1(X25),X24)|k7_relat_1(X25,X24)=k1_xboole_0|~v1_relat_1(X25))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t95_relat_1])])])).
% 0.20/0.45  fof(c_0_9, plain, ![X27, X28, X30]:(((v1_relat_1(esk7_2(X27,X28))&v1_funct_1(esk7_2(X27,X28)))&k1_relat_1(esk7_2(X27,X28))=X27)&(~r2_hidden(X30,X27)|k1_funct_1(esk7_2(X27,X28),X30)=X28)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.20/0.45  fof(c_0_10, plain, ![X26]:(~v1_relat_1(X26)|k7_relat_1(X26,k1_relat_1(X26))=X26), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t98_relat_1])])).
% 0.20/0.45  cnf(c_0_11, plain, (k7_relat_1(X1,X2)=k1_xboole_0|~r1_xboole_0(k1_relat_1(X1),X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.45  cnf(c_0_12, plain, (k1_relat_1(esk7_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.45  cnf(c_0_13, plain, (v1_relat_1(esk7_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.45  fof(c_0_14, plain, ![X9]:((r1_xboole_0(X9,X9)|X9!=k1_xboole_0)&(X9=k1_xboole_0|~r1_xboole_0(X9,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_xboole_1])])])).
% 0.20/0.45  cnf(c_0_15, plain, (k7_relat_1(X1,k1_relat_1(X1))=X1|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.45  cnf(c_0_16, plain, (k7_relat_1(esk7_2(X1,X2),X3)=k1_xboole_0|~r1_xboole_0(X1,X3)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_12]), c_0_13])])).
% 0.20/0.45  cnf(c_0_17, plain, (r1_xboole_0(X1,X1)|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.45  fof(c_0_18, plain, ![X31, X33]:(((v1_relat_1(esk8_1(X31))&v1_funct_1(esk8_1(X31)))&k1_relat_1(esk8_1(X31))=X31)&(~r2_hidden(X33,X31)|k1_funct_1(esk8_1(X31),X33)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.20/0.45  fof(c_0_19, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.20/0.45  fof(c_0_20, plain, ![X10, X11, X12, X14, X15, X16, X17, X19]:(((~r2_hidden(X12,X11)|r2_hidden(k4_tarski(X12,esk2_3(X10,X11,X12)),X10)|X11!=k1_relat_1(X10))&(~r2_hidden(k4_tarski(X14,X15),X10)|r2_hidden(X14,X11)|X11!=k1_relat_1(X10)))&((~r2_hidden(esk3_2(X16,X17),X17)|~r2_hidden(k4_tarski(esk3_2(X16,X17),X19),X16)|X17=k1_relat_1(X16))&(r2_hidden(esk3_2(X16,X17),X17)|r2_hidden(k4_tarski(esk3_2(X16,X17),esk4_2(X16,X17)),X16)|X17=k1_relat_1(X16)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_relat_1])])])])])])).
% 0.20/0.45  cnf(c_0_21, plain, (esk7_2(X1,X2)=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_13]), c_0_12])])).
% 0.20/0.45  cnf(c_0_22, plain, (r1_xboole_0(k1_xboole_0,k1_xboole_0)), inference(er,[status(thm)],[c_0_17])).
% 0.20/0.45  cnf(c_0_23, plain, (k1_relat_1(esk8_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.45  cnf(c_0_24, plain, (v1_relat_1(esk8_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.45  fof(c_0_25, negated_conjecture, ![X35, X36]:((~v1_relat_1(X35)|~v1_funct_1(X35)|(~v1_relat_1(X36)|~v1_funct_1(X36)|(k1_relat_1(X35)!=esk9_0|k1_relat_1(X36)!=esk9_0|X35=X36)))&esk9_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_19])])])])).
% 0.20/0.45  fof(c_0_26, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.45  cnf(c_0_27, plain, (r2_hidden(k4_tarski(X1,esk2_3(X3,X2,X1)),X3)|~r2_hidden(X1,X2)|X2!=k1_relat_1(X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_28, plain, (k1_funct_1(esk7_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.45  cnf(c_0_29, plain, (esk7_2(k1_xboole_0,X1)=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.45  cnf(c_0_30, plain, (k7_relat_1(esk8_1(X1),X2)=k1_xboole_0|~r1_xboole_0(X1,X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11, c_0_23]), c_0_24])])).
% 0.20/0.45  cnf(c_0_31, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk9_0|k1_relat_1(X2)!=esk9_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.45  cnf(c_0_32, plain, (v1_funct_1(esk8_1(X1))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.45  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.45  cnf(c_0_34, plain, (r2_hidden(k4_tarski(X1,esk2_3(X2,k1_relat_1(X2),X1)),X2)|~r2_hidden(X1,k1_relat_1(X2))), inference(er,[status(thm)],[c_0_27])).
% 0.20/0.45  cnf(c_0_35, plain, (k1_funct_1(k1_xboole_0,X1)=X2|~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.45  cnf(c_0_36, plain, (X1=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.45  cnf(c_0_37, plain, (r1_xboole_0(k1_relat_1(X1),X2)|k7_relat_1(X1,X2)!=k1_xboole_0|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.45  cnf(c_0_38, plain, (esk8_1(X1)=k1_xboole_0|~r1_xboole_0(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_30]), c_0_24]), c_0_23])])).
% 0.20/0.45  cnf(c_0_39, negated_conjecture, (X1=esk8_1(esk9_0)|k1_relat_1(X1)!=esk9_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_23]), c_0_32]), c_0_24])])])).
% 0.20/0.45  cnf(c_0_40, plain, (v1_funct_1(esk7_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.45  cnf(c_0_41, plain, (~r2_hidden(X1,k1_relat_1(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.45  cnf(c_0_42, plain, (X1=X2|~r2_hidden(X3,k1_xboole_0)), inference(spm,[status(thm)],[c_0_35, c_0_35])).
% 0.20/0.45  cnf(c_0_43, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.45  cnf(c_0_44, plain, (k1_relat_1(X1)=k1_xboole_0|k7_relat_1(X1,k1_relat_1(X1))!=k1_xboole_0|~v1_relat_1(X1)), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.20/0.45  cnf(c_0_45, plain, (esk8_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_38, c_0_22])).
% 0.20/0.45  cnf(c_0_46, negated_conjecture, (esk7_2(esk9_0,X1)=esk8_1(esk9_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_12]), c_0_40]), c_0_13])])])).
% 0.20/0.45  cnf(c_0_47, plain, (~r2_hidden(X1,k1_relat_1(k1_relat_1(X2)))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_41, c_0_34])).
% 0.20/0.45  cnf(c_0_48, plain, (r2_hidden(esk3_2(X1,X2),X2)|r2_hidden(k4_tarski(esk3_2(X1,X2),esk4_2(X1,X2)),X1)|X2=k1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.45  cnf(c_0_49, negated_conjecture, (esk9_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.45  cnf(c_0_50, plain, (X1=X2|v1_xboole_0(k1_xboole_0)), inference(spm,[status(thm)],[c_0_42, c_0_43])).
% 0.20/0.45  cnf(c_0_51, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0|~v1_relat_1(k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_15])])).
% 0.20/0.45  cnf(c_0_52, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_24, c_0_45])).
% 0.20/0.45  cnf(c_0_53, negated_conjecture, (k1_funct_1(esk8_1(esk9_0),X1)=X2|~r2_hidden(X1,esk9_0)), inference(spm,[status(thm)],[c_0_28, c_0_46])).
% 0.20/0.45  cnf(c_0_54, plain, (X1=k1_relat_1(k1_relat_1(k1_relat_1(X2)))|r2_hidden(esk3_2(k1_relat_1(k1_relat_1(X2)),X1),X1)|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.45  cnf(c_0_55, negated_conjecture, (v1_xboole_0(k1_xboole_0)), inference(er,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50])])).
% 0.20/0.45  cnf(c_0_56, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_51, c_0_52])])).
% 0.20/0.45  cnf(c_0_57, negated_conjecture, (X1=X2|~r2_hidden(X3,esk9_0)), inference(spm,[status(thm)],[c_0_53, c_0_53])).
% 0.20/0.45  cnf(c_0_58, negated_conjecture, (X1=k1_xboole_0|r2_hidden(esk3_2(k1_xboole_0,X1),X1)), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56]), c_0_56]), c_0_56]), c_0_56]), c_0_56])).
% 0.20/0.45  cnf(c_0_59, negated_conjecture, (X1=X2), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_49])).
% 0.20/0.45  cnf(c_0_60, negated_conjecture, ($false), inference(sr,[status(thm)],[c_0_49, c_0_59]), ['proof']).
% 0.20/0.45  # SZS output end CNFRefutation
% 0.20/0.45  # Proof object total steps             : 61
% 0.20/0.45  # Proof object clause steps            : 44
% 0.20/0.45  # Proof object formula steps           : 17
% 0.20/0.45  # Proof object conjectures             : 13
% 0.20/0.45  # Proof object clause conjectures      : 10
% 0.20/0.45  # Proof object formula conjectures     : 3
% 0.20/0.45  # Proof object initial clauses used    : 18
% 0.20/0.45  # Proof object initial formulas used   : 8
% 0.20/0.45  # Proof object generating inferences   : 22
% 0.20/0.45  # Proof object simplifying inferences  : 31
% 0.20/0.45  # Training examples: 0 positive, 0 negative
% 0.20/0.45  # Parsed axioms                        : 9
% 0.20/0.45  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.45  # Initial clauses                      : 22
% 0.20/0.45  # Removed in clause preprocessing      : 0
% 0.20/0.45  # Initial clauses in saturation        : 22
% 0.20/0.45  # Processed clauses                    : 460
% 0.20/0.45  # ...of these trivial                  : 5
% 0.20/0.45  # ...subsumed                          : 167
% 0.20/0.45  # ...remaining for further processing  : 288
% 0.20/0.45  # Other redundant clauses eliminated   : 94
% 0.20/0.45  # Clauses deleted for lack of memory   : 0
% 0.20/0.45  # Backward-subsumed                    : 87
% 0.20/0.45  # Backward-rewritten                   : 14
% 0.20/0.45  # Generated clauses                    : 6933
% 0.20/0.45  # ...of the previous two non-trivial   : 5002
% 0.20/0.45  # Contextual simplify-reflections      : 1
% 0.20/0.45  # Paramodulations                      : 6800
% 0.20/0.45  # Factorizations                       : 2
% 0.20/0.45  # Equation resolutions                 : 94
% 0.20/0.45  # Propositional unsat checks           : 0
% 0.20/0.45  #    Propositional check models        : 0
% 0.20/0.45  #    Propositional check unsatisfiable : 0
% 0.20/0.45  #    Propositional clauses             : 0
% 0.20/0.45  #    Propositional clauses after purity: 0
% 0.20/0.45  #    Propositional unsat core size     : 0
% 0.20/0.45  #    Propositional preprocessing time  : 0.000
% 0.20/0.45  #    Propositional encoding time       : 0.000
% 0.20/0.45  #    Propositional solver time         : 0.000
% 0.20/0.45  #    Success case prop preproc time    : 0.000
% 0.20/0.45  #    Success case prop encoding time   : 0.000
% 0.20/0.45  #    Success case prop solver time     : 0.000
% 0.20/0.45  # Current number of processed clauses  : 125
% 0.20/0.45  #    Positive orientable unit clauses  : 30
% 0.20/0.45  #    Positive unorientable unit clauses: 1
% 0.20/0.45  #    Negative unit clauses             : 29
% 0.20/0.45  #    Non-unit-clauses                  : 65
% 0.20/0.45  # Current number of unprocessed clauses: 3318
% 0.20/0.45  # ...number of literals in the above   : 9637
% 0.20/0.45  # Current number of archived formulas  : 0
% 0.20/0.45  # Current number of archived clauses   : 160
% 0.20/0.45  # Clause-clause subsumption calls (NU) : 4440
% 0.20/0.45  # Rec. Clause-clause subsumption calls : 3429
% 0.20/0.45  # Non-unit clause-clause subsumptions  : 151
% 0.20/0.45  # Unit Clause-clause subsumption calls : 497
% 0.20/0.45  # Rewrite failures with RHS unbound    : 316
% 0.20/0.45  # BW rewrite match attempts            : 532
% 0.20/0.45  # BW rewrite match successes           : 240
% 0.20/0.45  # Condensation attempts                : 0
% 0.20/0.45  # Condensation successes               : 0
% 0.20/0.45  # Termbank termtop insertions          : 64013
% 0.20/0.45  
% 0.20/0.45  # -------------------------------------------------
% 0.20/0.45  # User time                : 0.096 s
% 0.20/0.45  # System time              : 0.008 s
% 0.20/0.45  # Total time               : 0.104 s
% 0.20/0.45  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
