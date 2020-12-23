%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:52:59 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 132 expanded)
%              Number of clauses        :   31 (  56 expanded)
%              Number of leaves         :    9 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  130 ( 476 expanded)
%              Number of equality atoms :   41 ( 188 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_funct_1)).

fof(s3_funct_1__e7_25__funct_1,axiom,(
    ! [X1] :
    ? [X2] :
      ( v1_relat_1(X2)
      & v1_funct_1(X2)
      & k1_relat_1(X2) = X1
      & ! [X3] :
          ( r2_hidden(X3,X1)
         => k1_funct_1(X2,X3) = np__1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e7_25__funct_1)).

fof(d2_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> r2_hidden(X2,X1) ) )
      & ( v1_xboole_0(X1)
       => ( m1_subset_1(X2,X1)
        <=> v1_xboole_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(dt_o_1_0_setfam_1,axiom,(
    ! [X1] : m1_subset_1(o_1_0_setfam_1(X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_1_0_setfam_1)).

fof(t7_xboole_0,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

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

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(spc1_boole,axiom,(
    ~ v1_xboole_0(np__1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',spc1_boole)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,negated_conjecture,(
    ! [X100,X101] :
      ( ( ~ v1_relat_1(X100)
        | ~ v1_funct_1(X100)
        | ~ v1_relat_1(X101)
        | ~ v1_funct_1(X101)
        | k1_relat_1(X100) != esk7_0
        | k1_relat_1(X101) != esk7_0
        | X100 = X101 )
      & esk7_0 != k1_xboole_0 ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).

fof(c_0_11,plain,(
    ! [X96,X98] :
      ( v1_relat_1(esk6_1(X96))
      & v1_funct_1(esk6_1(X96))
      & k1_relat_1(esk6_1(X96)) = X96
      & ( ~ r2_hidden(X98,X96)
        | k1_funct_1(esk6_1(X96),X98) = np__1 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).

fof(c_0_12,plain,(
    ! [X52,X53] :
      ( ( ~ m1_subset_1(X53,X52)
        | r2_hidden(X53,X52)
        | v1_xboole_0(X52) )
      & ( ~ r2_hidden(X53,X52)
        | m1_subset_1(X53,X52)
        | v1_xboole_0(X52) )
      & ( ~ m1_subset_1(X53,X52)
        | v1_xboole_0(X53)
        | ~ v1_xboole_0(X52) )
      & ( ~ v1_xboole_0(X53)
        | m1_subset_1(X53,X52)
        | ~ v1_xboole_0(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).

fof(c_0_13,plain,(
    ! [X80] : m1_subset_1(o_1_0_setfam_1(X80),X80) ),
    inference(variable_rename,[status(thm)],[dt_o_1_0_setfam_1])).

fof(c_0_14,plain,(
    ! [X21] :
      ( X21 = k1_xboole_0
      | r2_hidden(esk2_1(X21),X21) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).

cnf(c_0_15,negated_conjecture,
    ( X1 = X2
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X2)
    | ~ v1_funct_1(X2)
    | k1_relat_1(X1) != esk7_0
    | k1_relat_1(X2) != esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,plain,
    ( k1_relat_1(esk6_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( v1_funct_1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,plain,
    ( v1_relat_1(esk6_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X93,X95] :
      ( v1_relat_1(esk5_1(X93))
      & v1_funct_1(esk5_1(X93))
      & k1_relat_1(esk5_1(X93)) = X93
      & ( ~ r2_hidden(X95,X93)
        | k1_funct_1(esk5_1(X93),X95) = k1_xboole_0 ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).

fof(c_0_20,plain,(
    ! [X13,X14,X15] :
      ( ( ~ v1_xboole_0(X13)
        | ~ r2_hidden(X14,X13) )
      & ( r2_hidden(esk1_1(X15),X15)
        | v1_xboole_0(X15) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | ~ m1_subset_1(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( m1_subset_1(o_1_0_setfam_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_23,plain,
    ( k1_funct_1(esk6_1(X2),X1) = np__1
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_24,plain,
    ( X1 = k1_xboole_0
    | r2_hidden(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( X1 = esk6_1(esk7_0)
    | k1_relat_1(X1) != esk7_0
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])])])).

cnf(c_0_26,plain,
    ( v1_funct_1(esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( k1_relat_1(esk5_1(X1)) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,plain,
    ( v1_relat_1(esk5_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,plain,
    ( v1_xboole_0(o_1_0_setfam_1(X1))
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

fof(c_0_31,plain,(
    ~ v1_xboole_0(np__1) ),
    inference(fof_simplification,[status(thm)],[spc1_boole])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,plain,
    ( k1_funct_1(esk5_1(X2),X1) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( k1_funct_1(esk6_1(X1),esk2_1(X1)) = np__1
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,negated_conjecture,
    ( esk6_1(esk7_0) = esk5_1(esk7_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27]),c_0_28])])])).

cnf(c_0_36,negated_conjecture,
    ( esk7_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_37,plain,
    ( ~ r2_hidden(X1,o_1_0_setfam_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_38,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_39,plain,
    ( ~ v1_xboole_0(np__1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_40,plain,
    ( r2_hidden(o_1_0_setfam_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_22])).

cnf(c_0_41,plain,
    ( k1_funct_1(esk5_1(X1),esk2_1(X1)) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_33,c_0_24])).

cnf(c_0_42,negated_conjecture,
    ( k1_funct_1(esk5_1(esk7_0),esk2_1(esk7_0)) = np__1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,o_1_0_setfam_1(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_44,plain,
    ( r2_hidden(o_1_0_setfam_1(np__1),np__1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( np__1 = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_36])).

cnf(c_0_46,plain,
    ( o_1_0_setfam_1(k1_xboole_0) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_43,c_0_24])).

cnf(c_0_47,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_38])).

cnf(c_0_48,plain,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_45]),c_0_47]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.19/0.35  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.50  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S032I
% 0.19/0.50  # and selection function SelectUnlessUniqMax.
% 0.19/0.50  #
% 0.19/0.50  # Preprocessing time       : 0.022 s
% 0.19/0.50  # Presaturation interreduction done
% 0.19/0.50  
% 0.19/0.50  # Proof found!
% 0.19/0.50  # SZS status Theorem
% 0.19/0.50  # SZS output start CNFRefutation
% 0.19/0.50  fof(t16_funct_1, conjecture, ![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_funct_1)).
% 0.19/0.50  fof(s3_funct_1__e7_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=np__1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e7_25__funct_1)).
% 0.19/0.50  fof(d2_subset_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))=>(m1_subset_1(X2,X1)<=>r2_hidden(X2,X1)))&(v1_xboole_0(X1)=>(m1_subset_1(X2,X1)<=>v1_xboole_0(X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 0.19/0.50  fof(dt_o_1_0_setfam_1, axiom, ![X1]:m1_subset_1(o_1_0_setfam_1(X1),X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_1_0_setfam_1)).
% 0.19/0.50  fof(t7_xboole_0, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~(r2_hidden(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 0.19/0.50  fof(s3_funct_1__e2_25__funct_1, axiom, ![X1]:?[X2]:(((v1_relat_1(X2)&v1_funct_1(X2))&k1_relat_1(X2)=X1)&![X3]:(r2_hidden(X3,X1)=>k1_funct_1(X2,X3)=k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', s3_funct_1__e2_25__funct_1)).
% 0.19/0.50  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.19/0.50  fof(spc1_boole, axiom, ~(v1_xboole_0(np__1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', spc1_boole)).
% 0.19/0.50  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.19/0.50  fof(c_0_9, negated_conjecture, ~(![X1]:(![X2]:((v1_relat_1(X2)&v1_funct_1(X2))=>![X3]:((v1_relat_1(X3)&v1_funct_1(X3))=>((k1_relat_1(X2)=X1&k1_relat_1(X3)=X1)=>X2=X3)))=>X1=k1_xboole_0)), inference(assume_negation,[status(cth)],[t16_funct_1])).
% 0.19/0.50  fof(c_0_10, negated_conjecture, ![X100, X101]:((~v1_relat_1(X100)|~v1_funct_1(X100)|(~v1_relat_1(X101)|~v1_funct_1(X101)|(k1_relat_1(X100)!=esk7_0|k1_relat_1(X101)!=esk7_0|X100=X101)))&esk7_0!=k1_xboole_0), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_9])])])])).
% 0.19/0.50  fof(c_0_11, plain, ![X96, X98]:(((v1_relat_1(esk6_1(X96))&v1_funct_1(esk6_1(X96)))&k1_relat_1(esk6_1(X96))=X96)&(~r2_hidden(X98,X96)|k1_funct_1(esk6_1(X96),X98)=np__1)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e7_25__funct_1])])])])).
% 0.19/0.50  fof(c_0_12, plain, ![X52, X53]:(((~m1_subset_1(X53,X52)|r2_hidden(X53,X52)|v1_xboole_0(X52))&(~r2_hidden(X53,X52)|m1_subset_1(X53,X52)|v1_xboole_0(X52)))&((~m1_subset_1(X53,X52)|v1_xboole_0(X53)|~v1_xboole_0(X52))&(~v1_xboole_0(X53)|m1_subset_1(X53,X52)|~v1_xboole_0(X52)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_subset_1])])])])).
% 0.19/0.50  fof(c_0_13, plain, ![X80]:m1_subset_1(o_1_0_setfam_1(X80),X80), inference(variable_rename,[status(thm)],[dt_o_1_0_setfam_1])).
% 0.19/0.50  fof(c_0_14, plain, ![X21]:(X21=k1_xboole_0|r2_hidden(esk2_1(X21),X21)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t7_xboole_0])])])])).
% 0.19/0.50  cnf(c_0_15, negated_conjecture, (X1=X2|~v1_relat_1(X1)|~v1_funct_1(X1)|~v1_relat_1(X2)|~v1_funct_1(X2)|k1_relat_1(X1)!=esk7_0|k1_relat_1(X2)!=esk7_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.50  cnf(c_0_16, plain, (k1_relat_1(esk6_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.50  cnf(c_0_17, plain, (v1_funct_1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.50  cnf(c_0_18, plain, (v1_relat_1(esk6_1(X1))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.50  fof(c_0_19, plain, ![X93, X95]:(((v1_relat_1(esk5_1(X93))&v1_funct_1(esk5_1(X93)))&k1_relat_1(esk5_1(X93))=X93)&(~r2_hidden(X95,X93)|k1_funct_1(esk5_1(X93),X95)=k1_xboole_0)), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[s3_funct_1__e2_25__funct_1])])])])).
% 0.19/0.50  fof(c_0_20, plain, ![X13, X14, X15]:((~v1_xboole_0(X13)|~r2_hidden(X14,X13))&(r2_hidden(esk1_1(X15),X15)|v1_xboole_0(X15))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.19/0.50  cnf(c_0_21, plain, (v1_xboole_0(X1)|~m1_subset_1(X1,X2)|~v1_xboole_0(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.50  cnf(c_0_22, plain, (m1_subset_1(o_1_0_setfam_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.50  cnf(c_0_23, plain, (k1_funct_1(esk6_1(X2),X1)=np__1|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.19/0.50  cnf(c_0_24, plain, (X1=k1_xboole_0|r2_hidden(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.50  cnf(c_0_25, negated_conjecture, (X1=esk6_1(esk7_0)|k1_relat_1(X1)!=esk7_0|~v1_funct_1(X1)|~v1_relat_1(X1)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18])])])).
% 0.19/0.50  cnf(c_0_26, plain, (v1_funct_1(esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.50  cnf(c_0_27, plain, (k1_relat_1(esk5_1(X1))=X1), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.50  cnf(c_0_28, plain, (v1_relat_1(esk5_1(X1))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.50  cnf(c_0_29, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.50  cnf(c_0_30, plain, (v1_xboole_0(o_1_0_setfam_1(X1))|~v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.50  fof(c_0_31, plain, ~v1_xboole_0(np__1), inference(fof_simplification,[status(thm)],[spc1_boole])).
% 0.19/0.50  cnf(c_0_32, plain, (r2_hidden(X1,X2)|v1_xboole_0(X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.50  cnf(c_0_33, plain, (k1_funct_1(esk5_1(X2),X1)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.50  cnf(c_0_34, plain, (k1_funct_1(esk6_1(X1),esk2_1(X1))=np__1|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.50  cnf(c_0_35, negated_conjecture, (esk6_1(esk7_0)=esk5_1(esk7_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_26]), c_0_27]), c_0_28])])])).
% 0.19/0.50  cnf(c_0_36, negated_conjecture, (esk7_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.19/0.50  cnf(c_0_37, plain, (~r2_hidden(X1,o_1_0_setfam_1(X2))|~v1_xboole_0(X2)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.50  cnf(c_0_38, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.19/0.50  cnf(c_0_39, plain, (~v1_xboole_0(np__1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.50  cnf(c_0_40, plain, (r2_hidden(o_1_0_setfam_1(X1),X1)|v1_xboole_0(X1)), inference(spm,[status(thm)],[c_0_32, c_0_22])).
% 0.19/0.50  cnf(c_0_41, plain, (k1_funct_1(esk5_1(X1),esk2_1(X1))=k1_xboole_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_33, c_0_24])).
% 0.19/0.50  cnf(c_0_42, negated_conjecture, (k1_funct_1(esk5_1(esk7_0),esk2_1(esk7_0))=np__1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36])).
% 0.19/0.50  cnf(c_0_43, plain, (~r2_hidden(X1,o_1_0_setfam_1(k1_xboole_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.19/0.50  cnf(c_0_44, plain, (r2_hidden(o_1_0_setfam_1(np__1),np__1)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.50  cnf(c_0_45, negated_conjecture, (np__1=k1_xboole_0), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_36])).
% 0.19/0.50  cnf(c_0_46, plain, (o_1_0_setfam_1(k1_xboole_0)=k1_xboole_0), inference(spm,[status(thm)],[c_0_43, c_0_24])).
% 0.19/0.50  cnf(c_0_47, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_29, c_0_38])).
% 0.19/0.50  cnf(c_0_48, plain, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_45]), c_0_47]), ['proof']).
% 0.19/0.50  # SZS output end CNFRefutation
% 0.19/0.50  # Proof object total steps             : 49
% 0.19/0.50  # Proof object clause steps            : 31
% 0.19/0.50  # Proof object formula steps           : 18
% 0.19/0.50  # Proof object conjectures             : 9
% 0.19/0.50  # Proof object clause conjectures      : 6
% 0.19/0.50  # Proof object formula conjectures     : 3
% 0.19/0.50  # Proof object initial clauses used    : 17
% 0.19/0.50  # Proof object initial formulas used   : 9
% 0.19/0.50  # Proof object generating inferences   : 13
% 0.19/0.50  # Proof object simplifying inferences  : 14
% 0.19/0.50  # Training examples: 0 positive, 0 negative
% 0.19/0.50  # Parsed axioms                        : 34
% 0.19/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.50  # Initial clauses                      : 68
% 0.19/0.50  # Removed in clause preprocessing      : 8
% 0.19/0.50  # Initial clauses in saturation        : 60
% 0.19/0.50  # Processed clauses                    : 1779
% 0.19/0.50  # ...of these trivial                  : 2
% 0.19/0.50  # ...subsumed                          : 1018
% 0.19/0.50  # ...remaining for further processing  : 759
% 0.19/0.50  # Other redundant clauses eliminated   : 24
% 0.19/0.50  # Clauses deleted for lack of memory   : 0
% 0.19/0.50  # Backward-subsumed                    : 1
% 0.19/0.50  # Backward-rewritten                   : 24
% 0.19/0.50  # Generated clauses                    : 8015
% 0.19/0.50  # ...of the previous two non-trivial   : 7617
% 0.19/0.50  # Contextual simplify-reflections      : 1
% 0.19/0.50  # Paramodulations                      : 7999
% 0.19/0.50  # Factorizations                       : 0
% 0.19/0.50  # Equation resolutions                 : 24
% 0.19/0.50  # Propositional unsat checks           : 0
% 0.19/0.50  #    Propositional check models        : 0
% 0.19/0.50  #    Propositional check unsatisfiable : 0
% 0.19/0.50  #    Propositional clauses             : 0
% 0.19/0.50  #    Propositional clauses after purity: 0
% 0.19/0.50  #    Propositional unsat core size     : 0
% 0.19/0.50  #    Propositional preprocessing time  : 0.000
% 0.19/0.50  #    Propositional encoding time       : 0.000
% 0.19/0.50  #    Propositional solver time         : 0.000
% 0.19/0.50  #    Success case prop preproc time    : 0.000
% 0.19/0.50  #    Success case prop encoding time   : 0.000
% 0.19/0.50  #    Success case prop solver time     : 0.000
% 0.19/0.50  # Current number of processed clauses  : 665
% 0.19/0.50  #    Positive orientable unit clauses  : 58
% 0.19/0.50  #    Positive unorientable unit clauses: 1
% 0.19/0.50  #    Negative unit clauses             : 5
% 0.19/0.50  #    Non-unit-clauses                  : 601
% 0.19/0.50  # Current number of unprocessed clauses: 5930
% 0.19/0.50  # ...number of literals in the above   : 12482
% 0.19/0.50  # Current number of archived formulas  : 0
% 0.19/0.50  # Current number of archived clauses   : 93
% 0.19/0.50  # Clause-clause subsumption calls (NU) : 66148
% 0.19/0.50  # Rec. Clause-clause subsumption calls : 52205
% 0.19/0.50  # Non-unit clause-clause subsumptions  : 683
% 0.19/0.50  # Unit Clause-clause subsumption calls : 1187
% 0.19/0.50  # Rewrite failures with RHS unbound    : 0
% 0.19/0.50  # BW rewrite match attempts            : 106
% 0.19/0.50  # BW rewrite match successes           : 20
% 0.19/0.50  # Condensation attempts                : 0
% 0.19/0.50  # Condensation successes               : 0
% 0.19/0.50  # Termbank termtop insertions          : 102554
% 0.19/0.50  
% 0.19/0.50  # -------------------------------------------------
% 0.19/0.50  # User time                : 0.139 s
% 0.19/0.50  # System time              : 0.012 s
% 0.19/0.50  # Total time               : 0.151 s
% 0.19/0.50  # Maximum resident set size: 1612 pages
%------------------------------------------------------------------------------
