%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:53:02 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 235 expanded)
%              Number of clauses        :   41 ( 106 expanded)
%              Number of leaves         :   11 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  188 ( 818 expanded)
%              Number of equality atoms :   76 ( 327 expanded)
%              Maximal formula depth    :   18 (   4 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_funct_1)).

fof(s3_funct_1__e2_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(fc8_relat_1,axiom,(
    ! [X1] :
      ( ( ~ v1_xboole_0(X1)
        & v1_relat_1(X1) )
     => ~ v1_xboole_0(k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(s3_funct_1__e7_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = np__1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(s3_funct_1__e2_24__funct_1,axiom,(
    ! [X1,X2] :
    ? [X3] :
      ( v1_relat_1(X3)
      & v1_funct_1(X3)
      & k1_relat_1(X3) = X1
      & ! [X4] :
          ( r2_hidden(X4,X1)
         => k1_funct_1(X3,X4) = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

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

fof(t152_zfmisc_1,axiom,(
    ! [X1,X2] : ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(d5_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( X2 = k2_relat_1(X1)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,k1_relat_1(X1))
                  & X3 = k1_funct_1(X1,X4) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_funct_1)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(c_0_11,negated_conjecture,(
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

fof(c_0_12,negated_conjecture,(
    ! [X32,X33] :
      ( ( ~ v1_relat_1(X32)
        | ~ v1_funct_1(X32)
        | ~ v1_relat_1(X33)
        | ~ v1_funct_1(X33)
        | k1_relat_1(X32) != esk7_0
        | k1_relat_1(X33) != esk7_0
        | X32 = X33 )
      & esk7_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_13,plain,(
    ! [X25,X27] :
      ( v1_relat_1(esk5_1(X25))
      & v1_funct_1(esk5_1(X25))
      & k1_relat_1(esk5_1(X25)) = X25
      & ( ~ r2_hidden(X27,X25)
        | k1_funct_1(esk5_1(X25),X27) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

fof(c_0_14,plain,(
    ! [X10] :
      ( v1_xboole_0(X10)
      | ~ v1_relat_1(X10)
      | ~ v1_xboole_0(k1_relat_1(X10)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).

fof(c_0_15,plain,(
    ! [X28,X30] :
      ( v1_relat_1(esk6_1(X28))
      & v1_funct_1(esk6_1(X28))
      & k1_relat_1(esk6_1(X28)) = X28
      & ( ~ r2_hidden(X30,X28)
        | k1_funct_1(esk6_1(X28),X30) = np__1 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).

cnf(c_0_16,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk7_0
    | k1_relat_1(X2) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( k1_relat_1(esk5_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,plain,
    ( v1_funct_1(esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_relat_1(esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_20,plain,(
    ! [X21,X22,X24] :
      ( v1_relat_1(esk4_2(X21,X22))
      & v1_funct_1(esk4_2(X21,X22))
      & k1_relat_1(esk4_2(X21,X22)) = X21
      & ( ~ r2_hidden(X24,X21)
        | k1_funct_1(esk4_2(X21,X22),X24) = X22 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).

fof(c_0_21,plain,(
    ! [X5] :
      ( ~ v1_xboole_0(X5)
      | X5 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).

cnf(c_0_22,plain,
    ( v1_xboole_0(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_xboole_0(k1_relat_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k1_relat_1(esk6_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v1_relat_1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk5_1(esk7_0)
    | k1_relat_1(X1) != esk7_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_18]),c_0_19])])])).

cnf(c_0_26,plain,
    ( k1_relat_1(esk4_2(X1,X2)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,plain,
    ( v1_funct_1(esk4_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( v1_relat_1(esk4_2(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( v1_xboole_0(esk6_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

fof(c_0_31,plain,(
    ! [X6,X7] :
      ( ( k2_zfmisc_1(X6,X7) != k1_xboole_0
        | X6 = k1_xboole_0
        | X7 = k1_xboole_0 )
      & ( X6 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 )
      & ( X7 != k1_xboole_0
        | k2_zfmisc_1(X6,X7) = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).

fof(c_0_32,plain,(
    ! [X8,X9] : ~ r2_hidden(X8,k2_zfmisc_1(X8,X9)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).

cnf(c_0_33,plain,
    ( k1_funct_1(esk4_2(X2,X3),X1) = X3
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,negated_conjecture,
    ( esk4_2(esk7_0,X1) = esk5_1(esk7_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])])).

cnf(c_0_35,plain,
    ( v1_funct_1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_36,plain,
    ( esk6_1(X1) = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,plain,
    ( k2_zfmisc_1(X2,X1) = k1_xboole_0
    | X1 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( ~ r2_hidden(X1,k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( k1_funct_1(esk5_1(esk7_0),X1) = X2
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_40,plain,(
    ! [X11,X12,X13,X15,X16,X17,X19] :
      ( ( r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X11))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( X13 = k1_funct_1(X11,esk1_3(X11,X12,X13))
        | ~ r2_hidden(X13,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(X16,k1_relat_1(X11))
        | X15 != k1_funct_1(X11,X16)
        | r2_hidden(X15,X12)
        | X12 != k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( ~ r2_hidden(esk2_2(X11,X17),X17)
        | ~ r2_hidden(X19,k1_relat_1(X11))
        | esk2_2(X11,X17) != k1_funct_1(X11,X19)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( r2_hidden(esk3_2(X11,X17),k1_relat_1(X11))
        | r2_hidden(esk2_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) )
      & ( esk2_2(X11,X17) = k1_funct_1(X11,esk3_2(X11,X17))
        | r2_hidden(esk2_2(X11,X17),X17)
        | X17 = k2_relat_1(X11)
        | ~ v1_relat_1(X11)
        | ~ v1_funct_1(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).

cnf(c_0_41,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_42,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_43,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_36])).

cnf(c_0_44,plain,
    ( k2_zfmisc_1(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(er,[status(thm)],[c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( X1 = esk6_1(esk7_0)
    | k1_relat_1(X1) != esk7_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_23]),c_0_35]),c_0_24])])])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_hidden(X1,k1_funct_1(esk5_1(esk7_0),X2))
    | ~ r2_hidden(X2,esk7_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))
    | r2_hidden(esk2_2(X1,X2),X2)
    | X2 = k2_relat_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_49,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_50,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_51,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_43,c_0_42])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( esk6_1(esk7_0) = esk5_1(esk7_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_17]),c_0_18]),c_0_19])])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r2_hidden(X1,esk7_0)
    | ~ r2_hidden(X2,X3) ),
    inference(spm,[status(thm)],[c_0_46,c_0_39])).

cnf(c_0_55,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_2(k1_xboole_0,X1),X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51])]),c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_57,negated_conjecture,
    ( esk5_1(esk7_0) = k1_xboole_0
    | ~ v1_xboole_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_hidden(X1,X2) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_59,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_57]),c_0_50]),c_0_56])).

cnf(c_0_60,plain,
    ( X1 = k1_xboole_0 ),
    inference(sr,[status(thm)],[c_0_55,c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59,c_0_60]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:37:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.13/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_funct_1)).
% 0.13/0.38  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.13/0.38  fof(fc8_relat_1, axiom, ![X1]:((~(v1_xboole_0(X1))&v1_relat_1(X1))=>~(v1_xboole_0(k1_relat_1(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 0.13/0.38  fof(s3_funct_1__e7_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=np__1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 0.13/0.38  fof(s3_funct_1__e2_24__funct_1, axiom, ![X1, X2]:?[X3]:(((v1_relat_1(X3)&v1_funct_1(X3))&k1_relat_1(X3)=X1)&![X4]:(r2_hidden(X4,X1)=>k1_funct_1(X3,X4)=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', s3_funct_1__e2_24__funct_1)).
% 0.13/0.38  fof(l13_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)=>X1=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 0.13/0.38  fof(t113_zfmisc_1, axiom, ![X1, X2]:(k2_zfmisc_1(X1,X2)=k1_xboole_0<=>(X1=k1_xboole_0|X2=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 0.13/0.38  fof(t152_zfmisc_1, axiom, ![X1, X2]:~(r2_hidden(X1,k2_zfmisc_1(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 0.13/0.38  fof(d5_funct_1, axiom, ![X1]:((v1_relat_1(X1)&v1_funct_1(X1))=>![X2]:(X2=k2_relat_1(X1)<=>![X3]:(r2_hidden(X3,X2)<=>?[X4]:(r2_hidden(X4,k1_relat_1(X1))&X3=k1_funct_1(X1,X4))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_funct_1)).
% 0.13/0.38  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.13/0.38  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.13/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.13/0.38  fof(c_0_12, negated_conjecture, ![X32, X33]:((~v1_relat_1(X32)|~v1_funct_1(X32)|(~v1_relat_1(X33)|~v1_funct_1(X33)|(k1_relat_1(X32)!=esk7_0|k1_relat_1(X33)!=esk7_0|X32=X33)))&esk7_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.13/0.38  fof(c_0_13, plain, ![X25, X27]:(((v1_relat_1(esk5_1(X25))&v1_funct_1(esk5_1(X25)))&k1_relat_1(esk5_1(X25))=X25)&(~r2_hidden(X27,X25)|k1_funct_1(esk5_1(X25),X27)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.13/0.38  fof(c_0_14, plain, ![X10]:(v1_xboole_0(X10)|~v1_relat_1(X10)|~v1_xboole_0(k1_relat_1(X10))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc8_relat_1])])])).
% 0.13/0.38  fof(c_0_15, plain, ![X28, X30]:(((v1_relat_1(esk6_1(X28))&v1_funct_1(esk6_1(X28)))&k1_relat_1(esk6_1(X28))=X28)&(~r2_hidden(X30,X28)|k1_funct_1(esk6_1(X28),X30)=np__1)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).
% 0.13/0.38  cnf(c_0_16, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk7_0|k1_relat_1(X2)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_17, plain, (k1_relat_1(esk5_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_18, plain, (v1_funct_1(esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_19, plain, (v1_relat_1(esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  fof(c_0_20, plain, ![X21, X22, X24]:(((v1_relat_1(esk4_2(X21,X22))&v1_funct_1(esk4_2(X21,X22)))&k1_relat_1(esk4_2(X21,X22))=X21)&(~r2_hidden(X24,X21)|k1_funct_1(esk4_2(X21,X22),X24)=X22)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_24__funct_1])])])])).
% 0.13/0.38  fof(c_0_21, plain, ![X5]:(~v1_xboole_0(X5)|X5=k1_xboole_0), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l13_xboole_0])])).
% 0.13/0.38  cnf(c_0_22, plain, (v1_xboole_0(X1)|~v1_relat_1(X1)|~v1_xboole_0(k1_relat_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.13/0.38  cnf(c_0_23, plain, (k1_relat_1(esk6_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_24, plain, (v1_relat_1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_25, negated_conjecture, (X1=esk5_1(esk7_0)|k1_relat_1(X1)!=esk7_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_18]), c_0_19])])])).
% 0.13/0.38  cnf(c_0_26, plain, (k1_relat_1(esk4_2(X1,X2))=X1), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_27, plain, (v1_funct_1(esk4_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_28, plain, (v1_relat_1(esk4_2(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_29, plain, (X1=k1_xboole_0|~v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_30, plain, (v1_xboole_0(esk6_1(X1))|~v1_xboole_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.13/0.38  fof(c_0_31, plain, ![X6, X7]:((k2_zfmisc_1(X6,X7)!=k1_xboole_0|(X6=k1_xboole_0|X7=k1_xboole_0))&((X6!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0)&(X7!=k1_xboole_0|k2_zfmisc_1(X6,X7)=k1_xboole_0))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t113_zfmisc_1])])])).
% 0.13/0.38  fof(c_0_32, plain, ![X8, X9]:~r2_hidden(X8,k2_zfmisc_1(X8,X9)), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[t152_zfmisc_1])])).
% 0.13/0.38  cnf(c_0_33, plain, (k1_funct_1(esk4_2(X2,X3),X1)=X3|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.13/0.38  cnf(c_0_34, negated_conjecture, (esk4_2(esk7_0,X1)=esk5_1(esk7_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])])).
% 0.13/0.38  cnf(c_0_35, plain, (v1_funct_1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.13/0.38  cnf(c_0_36, plain, (esk6_1(X1)=k1_xboole_0|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.38  cnf(c_0_37, plain, (k2_zfmisc_1(X2,X1)=k1_xboole_0|X1!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.38  cnf(c_0_38, plain, (~r2_hidden(X1,k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.13/0.38  cnf(c_0_39, negated_conjecture, (k1_funct_1(esk5_1(esk7_0),X1)=X2|~r2_hidden(X1,esk7_0)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.13/0.38  fof(c_0_40, plain, ![X11, X12, X13, X15, X16, X17, X19]:((((r2_hidden(esk1_3(X11,X12,X13),k1_relat_1(X11))|~r2_hidden(X13,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(X13=k1_funct_1(X11,esk1_3(X11,X12,X13))|~r2_hidden(X13,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&(~r2_hidden(X16,k1_relat_1(X11))|X15!=k1_funct_1(X11,X16)|r2_hidden(X15,X12)|X12!=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11))))&((~r2_hidden(esk2_2(X11,X17),X17)|(~r2_hidden(X19,k1_relat_1(X11))|esk2_2(X11,X17)!=k1_funct_1(X11,X19))|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&((r2_hidden(esk3_2(X11,X17),k1_relat_1(X11))|r2_hidden(esk2_2(X11,X17),X17)|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))&(esk2_2(X11,X17)=k1_funct_1(X11,esk3_2(X11,X17))|r2_hidden(esk2_2(X11,X17),X17)|X17=k2_relat_1(X11)|(~v1_relat_1(X11)|~v1_funct_1(X11)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_funct_1])])])])])])).
% 0.13/0.38  cnf(c_0_41, plain, (v1_funct_1(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.13/0.38  cnf(c_0_42, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.13/0.38  cnf(c_0_43, plain, (v1_relat_1(k1_xboole_0)|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_24, c_0_36])).
% 0.13/0.38  cnf(c_0_44, plain, (k2_zfmisc_1(X1,k1_xboole_0)=k1_xboole_0), inference(er,[status(thm)],[c_0_37])).
% 0.13/0.38  cnf(c_0_45, negated_conjecture, (X1=esk6_1(esk7_0)|k1_relat_1(X1)!=esk7_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_23]), c_0_35]), c_0_24])])])).
% 0.13/0.38  cnf(c_0_46, negated_conjecture, (~r2_hidden(X1,k1_funct_1(esk5_1(esk7_0),X2))|~r2_hidden(X2,esk7_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.13/0.38  cnf(c_0_47, plain, (r2_hidden(esk3_2(X1,X2),k1_relat_1(X1))|r2_hidden(esk2_2(X1,X2),X2)|X2=k2_relat_1(X1)|~v1_relat_1(X1)|~v1_funct_1(X1)), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.13/0.38  cnf(c_0_48, plain, (v1_funct_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.13/0.38  cnf(c_0_49, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.38  cnf(c_0_50, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.13/0.38  cnf(c_0_51, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_43, c_0_42])).
% 0.13/0.38  cnf(c_0_52, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_38, c_0_44])).
% 0.13/0.38  cnf(c_0_53, negated_conjecture, (esk6_1(esk7_0)=esk5_1(esk7_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_17]), c_0_18]), c_0_19])])])).
% 0.13/0.38  cnf(c_0_54, negated_conjecture, (~r2_hidden(X1,esk7_0)|~r2_hidden(X2,X3)), inference(spm,[status(thm)],[c_0_46, c_0_39])).
% 0.13/0.38  cnf(c_0_55, plain, (X1=k1_xboole_0|r2_hidden(esk2_2(k1_xboole_0,X1),X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51])]), c_0_52])).
% 0.13/0.38  cnf(c_0_56, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.13/0.38  cnf(c_0_57, negated_conjecture, (esk5_1(esk7_0)=k1_xboole_0|~v1_xboole_0(esk7_0)), inference(spm,[status(thm)],[c_0_36, c_0_53])).
% 0.13/0.38  cnf(c_0_58, negated_conjecture, (~r2_hidden(X1,X2)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])).
% 0.13/0.38  cnf(c_0_59, negated_conjecture, (~v1_xboole_0(esk7_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_57]), c_0_50]), c_0_56])).
% 0.13/0.38  cnf(c_0_60, plain, (X1=k1_xboole_0), inference(sr,[status(thm)],[c_0_55, c_0_58])).
% 0.13/0.38  cnf(c_0_61, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_59, c_0_60]), c_0_42])]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 62
% 0.13/0.38  # Proof object clause steps            : 41
% 0.13/0.38  # Proof object formula steps           : 21
% 0.13/0.38  # Proof object conjectures             : 16
% 0.13/0.38  # Proof object clause conjectures      : 13
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 20
% 0.13/0.38  # Proof object initial formulas used   : 11
% 0.13/0.38  # Proof object generating inferences   : 18
% 0.13/0.38  # Proof object simplifying inferences  : 31
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 11
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 29
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 29
% 0.13/0.38  # Processed clauses                    : 110
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 19
% 0.13/0.38  # ...remaining for further processing  : 91
% 0.13/0.38  # Other redundant clauses eliminated   : 15
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 3
% 0.13/0.38  # Backward-rewritten                   : 47
% 0.13/0.38  # Generated clauses                    : 171
% 0.13/0.38  # ...of the previous two non-trivial   : 149
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 156
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 15
% 0.13/0.38  # Propositional unsat checks           : 0
% 0.13/0.38  #    Propositional check models        : 0
% 0.13/0.38  #    Propositional check unsatisfiable : 0
% 0.13/0.38  #    Propositional clauses             : 0
% 0.13/0.38  #    Propositional clauses after purity: 0
% 0.13/0.38  #    Propositional unsat core size     : 0
% 0.13/0.38  #    Propositional preprocessing time  : 0.000
% 0.13/0.38  #    Propositional encoding time       : 0.000
% 0.13/0.38  #    Propositional solver time         : 0.000
% 0.13/0.38  #    Success case prop preproc time    : 0.000
% 0.13/0.38  #    Success case prop encoding time   : 0.000
% 0.13/0.38  #    Success case prop solver time     : 0.000
% 0.13/0.38  # Current number of processed clauses  : 6
% 0.13/0.38  #    Positive orientable unit clauses  : 3
% 0.13/0.38  #    Positive unorientable unit clauses: 1
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 0
% 0.13/0.38  # Current number of unprocessed clauses: 77
% 0.13/0.38  # ...number of literals in the above   : 241
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 80
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 111
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 76
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 10
% 0.13/0.38  # Unit Clause-clause subsumption calls : 46
% 0.13/0.38  # Rewrite failures with RHS unbound    : 3
% 0.13/0.38  # BW rewrite match attempts            : 41
% 0.13/0.38  # BW rewrite match successes           : 40
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 3624
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.032 s
% 0.13/0.38  # System time              : 0.005 s
% 0.13/0.38  # Total time               : 0.037 s
% 0.13/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
