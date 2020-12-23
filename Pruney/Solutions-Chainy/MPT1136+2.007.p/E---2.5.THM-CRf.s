%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:28 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 128 expanded)
%              Number of clauses        :   33 (  52 expanded)
%              Number of leaves         :   11 (  31 expanded)
%              Depth                    :   14
%              Number of atoms          :  159 ( 445 expanded)
%              Number of equality atoms :    7 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t24_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(d4_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_orders_2(X1)
      <=> r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

fof(d1_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_relat_2(X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(k4_tarski(X3,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(d1_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
    <=> ! [X2] :
          ~ ( r2_hidden(X2,X1)
            & ! [X3,X4] : X2 != k4_tarski(X3,X4) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r1_orders_2(X1,X2,X2) ) ) ),
    inference(assume_negation,[status(cth)],[t24_orders_2])).

fof(c_0_12,plain,(
    ! [X26] :
      ( ( ~ v3_orders_2(X26)
        | r1_relat_2(u1_orders_2(X26),u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( ~ r1_relat_2(u1_orders_2(X26),u1_struct_0(X26))
        | v3_orders_2(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & ~ r1_orders_2(esk5_0,esk6_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X20,X21,X22,X23] :
      ( ( ~ r1_relat_2(X20,X21)
        | ~ r2_hidden(X22,X21)
        | r2_hidden(k4_tarski(X22,X22),X20)
        | ~ v1_relat_1(X20) )
      & ( r2_hidden(esk4_2(X20,X23),X23)
        | r1_relat_2(X20,X23)
        | ~ v1_relat_1(X20) )
      & ( ~ r2_hidden(k4_tarski(esk4_2(X20,X23),esk4_2(X20,X23)),X20)
        | r1_relat_2(X20,X23)
        | ~ v1_relat_1(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).

cnf(c_0_15,plain,
    ( r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_16,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_17,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X8,X9)
      | v1_xboole_0(X9)
      | r2_hidden(X8,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_19,plain,(
    ! [X30] :
      ( ~ l1_orders_2(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_20,plain,(
    ! [X31] :
      ( ~ l1_orders_2(X31)
      | m1_subset_1(u1_orders_2(X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X31)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_21,plain,
    ( r2_hidden(k4_tarski(X3,X3),X1)
    | ~ r1_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r1_relat_2(u1_orders_2(esk5_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17])])).

fof(c_0_23,plain,(
    ! [X10,X11,X14,X16,X17] :
      ( ( ~ v1_relat_1(X10)
        | ~ r2_hidden(X11,X10)
        | X11 = k4_tarski(esk1_2(X10,X11),esk2_2(X10,X11)) )
      & ( r2_hidden(esk3_1(X14),X14)
        | v1_relat_1(X14) )
      & ( esk3_1(X14) != k4_tarski(X16,X17)
        | v1_relat_1(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).

fof(c_0_24,plain,(
    ! [X25] :
      ( v2_struct_0(X25)
      | ~ l1_struct_0(X25)
      | ~ v1_xboole_0(u1_struct_0(X25)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_25,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_27,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_28,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(X5))
      | ~ r2_hidden(X7,X6)
      | r2_hidden(X7,X5) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk5_0))
    | ~ v1_relat_1(u1_orders_2(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,plain,
    ( r2_hidden(esk3_1(X1),X1)
    | v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_17])).

cnf(c_0_35,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(u1_orders_2(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_17])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk3_1(u1_orders_2(esk5_0)),u1_orders_2(esk5_0))
    | r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0))
    | r2_hidden(esk3_1(u1_orders_2(esk5_0)),u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

fof(c_0_42,plain,(
    ! [X18,X19] : v1_relat_1(k2_zfmisc_1(X18,X19)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

cnf(c_0_43,plain,
    ( X2 = k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2))
    | ~ v1_relat_1(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(esk3_1(u1_orders_2(esk5_0)),k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))
    | r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_45,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_46,plain,
    ( v1_relat_1(X1)
    | esk3_1(X1) != k4_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_47,negated_conjecture,
    ( k4_tarski(esk1_2(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)),esk3_1(u1_orders_2(esk5_0))),esk2_2(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)),esk3_1(u1_orders_2(esk5_0)))) = esk3_1(u1_orders_2(esk5_0))
    | r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_45])])).

cnf(c_0_48,negated_conjecture,
    ( v1_relat_1(X1)
    | r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0))
    | esk3_1(X1) != esk3_1(u1_orders_2(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_49,negated_conjecture,
    ( v1_relat_1(u1_orders_2(esk5_0))
    | r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0)) ),
    inference(er,[status(thm)],[c_0_48])).

fof(c_0_50,plain,(
    ! [X27,X28,X29] :
      ( ( ~ r1_orders_2(X27,X28,X29)
        | r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) )
      & ( ~ r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))
        | r1_orders_2(X27,X28,X29)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X28,u1_struct_0(X27))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0))
    | r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk5_0))
    | ~ r2_hidden(X1,u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_49])).

cnf(c_0_52,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_51]),c_0_39])])).

cnf(c_0_54,negated_conjecture,
    ( ~ r1_orders_2(esk5_0,esk6_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_55,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_17]),c_0_26])]),c_0_54]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  # Version: 2.5pre002
% 0.19/0.35  # No SInE strategy applied
% 0.19/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S031A
% 0.19/0.38  # and selection function PSelectStrongRRNonRROptimalLit.
% 0.19/0.38  #
% 0.19/0.38  # Preprocessing time       : 0.027 s
% 0.19/0.38  # Presaturation interreduction done
% 0.19/0.38  
% 0.19/0.38  # Proof found!
% 0.19/0.38  # SZS status Theorem
% 0.19/0.38  # SZS output start CNFRefutation
% 0.19/0.38  fof(t24_orders_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 0.19/0.38  fof(d4_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v3_orders_2(X1)<=>r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_orders_2)).
% 0.19/0.38  fof(d1_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_relat_2(X1,X2)<=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(k4_tarski(X3,X3),X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_2)).
% 0.19/0.38  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.38  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.19/0.38  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.19/0.38  fof(d1_relat_1, axiom, ![X1]:(v1_relat_1(X1)<=>![X2]:~((r2_hidden(X2,X1)&![X3, X4]:X2!=k4_tarski(X3,X4)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 0.19/0.38  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.38  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_subset_1)).
% 0.19/0.38  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.19/0.38  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_orders_2)).
% 0.19/0.38  fof(c_0_11, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2)))), inference(assume_negation,[status(cth)],[t24_orders_2])).
% 0.19/0.38  fof(c_0_12, plain, ![X26]:((~v3_orders_2(X26)|r1_relat_2(u1_orders_2(X26),u1_struct_0(X26))|~l1_orders_2(X26))&(~r1_relat_2(u1_orders_2(X26),u1_struct_0(X26))|v3_orders_2(X26)|~l1_orders_2(X26))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).
% 0.19/0.38  fof(c_0_13, negated_conjecture, (((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&l1_orders_2(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&~r1_orders_2(esk5_0,esk6_0,esk6_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.19/0.38  fof(c_0_14, plain, ![X20, X21, X22, X23]:((~r1_relat_2(X20,X21)|(~r2_hidden(X22,X21)|r2_hidden(k4_tarski(X22,X22),X20))|~v1_relat_1(X20))&((r2_hidden(esk4_2(X20,X23),X23)|r1_relat_2(X20,X23)|~v1_relat_1(X20))&(~r2_hidden(k4_tarski(esk4_2(X20,X23),esk4_2(X20,X23)),X20)|r1_relat_2(X20,X23)|~v1_relat_1(X20)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).
% 0.19/0.38  cnf(c_0_15, plain, (r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.38  cnf(c_0_16, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_17, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  fof(c_0_18, plain, ![X8, X9]:(~m1_subset_1(X8,X9)|(v1_xboole_0(X9)|r2_hidden(X8,X9))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.38  fof(c_0_19, plain, ![X30]:(~l1_orders_2(X30)|l1_struct_0(X30)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.19/0.38  fof(c_0_20, plain, ![X31]:(~l1_orders_2(X31)|m1_subset_1(u1_orders_2(X31),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X31),u1_struct_0(X31))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.19/0.38  cnf(c_0_21, plain, (r2_hidden(k4_tarski(X3,X3),X1)|~r1_relat_2(X1,X2)|~r2_hidden(X3,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.38  cnf(c_0_22, negated_conjecture, (r1_relat_2(u1_orders_2(esk5_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17])])).
% 0.19/0.38  fof(c_0_23, plain, ![X10, X11, X14, X16, X17]:((~v1_relat_1(X10)|(~r2_hidden(X11,X10)|X11=k4_tarski(esk1_2(X10,X11),esk2_2(X10,X11))))&((r2_hidden(esk3_1(X14),X14)|v1_relat_1(X14))&(esk3_1(X14)!=k4_tarski(X16,X17)|v1_relat_1(X14)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_1])])])])])])).
% 0.19/0.38  fof(c_0_24, plain, ![X25]:(v2_struct_0(X25)|~l1_struct_0(X25)|~v1_xboole_0(u1_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.38  cnf(c_0_25, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.38  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_27, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.38  fof(c_0_28, plain, ![X5, X6, X7]:(~m1_subset_1(X6,k1_zfmisc_1(X5))|(~r2_hidden(X7,X6)|r2_hidden(X7,X5))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.19/0.38  cnf(c_0_29, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.38  cnf(c_0_30, negated_conjecture, (r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk5_0))|~v1_relat_1(u1_orders_2(esk5_0))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.38  cnf(c_0_31, plain, (r2_hidden(esk3_1(X1),X1)|v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_32, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.19/0.38  cnf(c_0_33, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|r2_hidden(esk6_0,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.38  cnf(c_0_34, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_27, c_0_17])).
% 0.19/0.38  cnf(c_0_35, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_36, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.38  cnf(c_0_37, negated_conjecture, (m1_subset_1(u1_orders_2(esk5_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_29, c_0_17])).
% 0.19/0.38  cnf(c_0_38, negated_conjecture, (r2_hidden(esk3_1(u1_orders_2(esk5_0)),u1_orders_2(esk5_0))|r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk5_0))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_31])).
% 0.19/0.38  cnf(c_0_39, negated_conjecture, (r2_hidden(esk6_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_34])]), c_0_35])).
% 0.19/0.38  cnf(c_0_40, negated_conjecture, (r2_hidden(X1,k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))|~r2_hidden(X1,u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.38  cnf(c_0_41, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0))|r2_hidden(esk3_1(u1_orders_2(esk5_0)),u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.38  fof(c_0_42, plain, ![X18, X19]:v1_relat_1(k2_zfmisc_1(X18,X19)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.19/0.38  cnf(c_0_43, plain, (X2=k4_tarski(esk1_2(X1,X2),esk2_2(X1,X2))|~v1_relat_1(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_44, negated_conjecture, (r2_hidden(esk3_1(u1_orders_2(esk5_0)),k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)))|r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_40, c_0_41])).
% 0.19/0.38  cnf(c_0_45, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.38  cnf(c_0_46, plain, (v1_relat_1(X1)|esk3_1(X1)!=k4_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.19/0.38  cnf(c_0_47, negated_conjecture, (k4_tarski(esk1_2(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)),esk3_1(u1_orders_2(esk5_0))),esk2_2(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(esk5_0)),esk3_1(u1_orders_2(esk5_0))))=esk3_1(u1_orders_2(esk5_0))|r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_45])])).
% 0.19/0.38  cnf(c_0_48, negated_conjecture, (v1_relat_1(X1)|r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0))|esk3_1(X1)!=esk3_1(u1_orders_2(esk5_0))), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.19/0.38  cnf(c_0_49, negated_conjecture, (v1_relat_1(u1_orders_2(esk5_0))|r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0))), inference(er,[status(thm)],[c_0_48])).
% 0.19/0.38  fof(c_0_50, plain, ![X27, X28, X29]:((~r1_orders_2(X27,X28,X29)|r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))&(~r2_hidden(k4_tarski(X28,X29),u1_orders_2(X27))|r1_orders_2(X27,X28,X29)|~m1_subset_1(X29,u1_struct_0(X27))|~m1_subset_1(X28,u1_struct_0(X27))|~l1_orders_2(X27))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.19/0.38  cnf(c_0_51, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0))|r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk5_0))|~r2_hidden(X1,u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_30, c_0_49])).
% 0.19/0.38  cnf(c_0_52, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(esk6_0,esk6_0),u1_orders_2(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(ef,[status(thm)],[c_0_51]), c_0_39])])).
% 0.19/0.38  cnf(c_0_54, negated_conjecture, (~r1_orders_2(esk5_0,esk6_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.38  cnf(c_0_55, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_17]), c_0_26])]), c_0_54]), ['proof']).
% 0.19/0.38  # SZS output end CNFRefutation
% 0.19/0.38  # Proof object total steps             : 56
% 0.19/0.38  # Proof object clause steps            : 33
% 0.19/0.38  # Proof object formula steps           : 23
% 0.19/0.38  # Proof object conjectures             : 24
% 0.19/0.38  # Proof object clause conjectures      : 21
% 0.19/0.38  # Proof object formula conjectures     : 3
% 0.19/0.38  # Proof object initial clauses used    : 17
% 0.19/0.38  # Proof object initial formulas used   : 11
% 0.19/0.38  # Proof object generating inferences   : 16
% 0.19/0.38  # Proof object simplifying inferences  : 13
% 0.19/0.38  # Training examples: 0 positive, 0 negative
% 0.19/0.38  # Parsed axioms                        : 11
% 0.19/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.38  # Initial clauses                      : 21
% 0.19/0.38  # Removed in clause preprocessing      : 0
% 0.19/0.38  # Initial clauses in saturation        : 21
% 0.19/0.38  # Processed clauses                    : 76
% 0.19/0.38  # ...of these trivial                  : 0
% 0.19/0.38  # ...subsumed                          : 1
% 0.19/0.38  # ...remaining for further processing  : 75
% 0.19/0.38  # Other redundant clauses eliminated   : 0
% 0.19/0.38  # Clauses deleted for lack of memory   : 0
% 0.19/0.38  # Backward-subsumed                    : 1
% 0.19/0.38  # Backward-rewritten                   : 9
% 0.19/0.38  # Generated clauses                    : 69
% 0.19/0.38  # ...of the previous two non-trivial   : 65
% 0.19/0.38  # Contextual simplify-reflections      : 0
% 0.19/0.38  # Paramodulations                      : 66
% 0.19/0.38  # Factorizations                       : 2
% 0.19/0.38  # Equation resolutions                 : 1
% 0.19/0.38  # Propositional unsat checks           : 0
% 0.19/0.38  #    Propositional check models        : 0
% 0.19/0.38  #    Propositional check unsatisfiable : 0
% 0.19/0.38  #    Propositional clauses             : 0
% 0.19/0.38  #    Propositional clauses after purity: 0
% 0.19/0.38  #    Propositional unsat core size     : 0
% 0.19/0.38  #    Propositional preprocessing time  : 0.000
% 0.19/0.38  #    Propositional encoding time       : 0.000
% 0.19/0.38  #    Propositional solver time         : 0.000
% 0.19/0.38  #    Success case prop preproc time    : 0.000
% 0.19/0.38  #    Success case prop encoding time   : 0.000
% 0.19/0.38  #    Success case prop solver time     : 0.000
% 0.19/0.38  # Current number of processed clauses  : 44
% 0.19/0.38  #    Positive orientable unit clauses  : 9
% 0.19/0.38  #    Positive unorientable unit clauses: 0
% 0.19/0.38  #    Negative unit clauses             : 2
% 0.19/0.38  #    Non-unit-clauses                  : 33
% 0.19/0.38  # Current number of unprocessed clauses: 28
% 0.19/0.38  # ...number of literals in the above   : 102
% 0.19/0.38  # Current number of archived formulas  : 0
% 0.19/0.38  # Current number of archived clauses   : 31
% 0.19/0.38  # Clause-clause subsumption calls (NU) : 278
% 0.19/0.38  # Rec. Clause-clause subsumption calls : 83
% 0.19/0.38  # Non-unit clause-clause subsumptions  : 1
% 0.19/0.38  # Unit Clause-clause subsumption calls : 4
% 0.19/0.38  # Rewrite failures with RHS unbound    : 0
% 0.19/0.38  # BW rewrite match attempts            : 2
% 0.19/0.38  # BW rewrite match successes           : 2
% 0.19/0.38  # Condensation attempts                : 0
% 0.19/0.38  # Condensation successes               : 0
% 0.19/0.38  # Termbank termtop insertions          : 3567
% 0.19/0.38  
% 0.19/0.38  # -------------------------------------------------
% 0.19/0.38  # User time                : 0.032 s
% 0.19/0.38  # System time              : 0.004 s
% 0.19/0.38  # Total time               : 0.036 s
% 0.19/0.38  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
