%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:11 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 131 expanded)
%              Number of clauses        :   29 (  58 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   10
%              Number of atoms          :  161 ( 337 expanded)
%              Number of equality atoms :   38 ( 106 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(l35_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(t9_mcart_1,axiom,(
    ! [X1] :
      ~ ( X1 != k1_xboole_0
        & ! [X2] :
            ~ ( r2_hidden(X2,X1)
              & ! [X3,X4] :
                  ~ ( ( r2_hidden(X3,X1)
                      | r2_hidden(X4,X1) )
                    & X2 = k4_tarski(X3,X4) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(t49_zfmisc_1,axiom,(
    ! [X1,X2] : k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t61_setfam_1,axiom,(
    ! [X1] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

fof(t21_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) = k1_xboole_0
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

fof(t142_funct_1,axiom,(
    ! [X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X1,k2_relat_1(X2))
      <=> k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(t172_relat_1,axiom,(
    ! [X1] : k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(t6_yellow_0,conjecture,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_yellow_0)).

fof(t60_relat_1,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(d8_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r1_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(d9_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( m1_subset_1(X3,u1_struct_0(X1))
         => ( r2_lattice3(X1,X2,X3)
          <=> ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r1_orders_2(X1,X4,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(c_0_14,plain,(
    ! [X6,X7] :
      ( ( k4_xboole_0(k1_tarski(X6),X7) != k1_xboole_0
        | r2_hidden(X6,X7) )
      & ( ~ r2_hidden(X6,X7)
        | k4_xboole_0(k1_tarski(X6),X7) = k1_xboole_0 ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).

fof(c_0_15,plain,(
    ! [X22,X24,X25] :
      ( ( r2_hidden(esk1_1(X22),X22)
        | X22 = k1_xboole_0 )
      & ( ~ r2_hidden(X24,X22)
        | esk1_1(X22) != k4_tarski(X24,X25)
        | X22 = k1_xboole_0 )
      & ( ~ r2_hidden(X25,X22)
        | esk1_1(X22) != k4_tarski(X24,X25)
        | X22 = k1_xboole_0 ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).

fof(c_0_16,plain,(
    ! [X10,X11] : k2_xboole_0(k1_tarski(X10),X11) != k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t49_zfmisc_1])).

fof(c_0_17,plain,(
    ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

fof(c_0_18,plain,(
    ! [X12,X13,X14] :
      ( ~ r2_hidden(X12,X13)
      | ~ m1_subset_1(X13,k1_zfmisc_1(X14))
      | m1_subset_1(X12,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_19,plain,(
    ! [X15] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X15))) ),
    inference(variable_rename,[status(thm)],[t61_setfam_1])).

fof(c_0_20,plain,(
    ! [X8,X9] :
      ( k4_xboole_0(k1_tarski(X8),k1_tarski(X9)) != k1_xboole_0
      | X8 = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_zfmisc_1])])).

cnf(c_0_21,plain,
    ( k4_xboole_0(k1_tarski(X1),X2) = k1_xboole_0
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | X1 = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_xboole_0(k1_tarski(X1),X2) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( X1 = X2
    | k4_xboole_0(k1_tarski(X1),k1_tarski(X2)) != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( k4_xboole_0(k1_tarski(esk1_1(X1)),X1) = k1_xboole_0
    | X1 = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_29,plain,
    ( k1_tarski(X1) != k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

fof(c_0_30,plain,(
    ! [X17,X18] :
      ( ( ~ r2_hidden(X17,k2_relat_1(X18))
        | k10_relat_1(X18,k1_tarski(X17)) != k1_xboole_0
        | ~ v1_relat_1(X18) )
      & ( k10_relat_1(X18,k1_tarski(X17)) = k1_xboole_0
        | r2_hidden(X17,k2_relat_1(X18))
        | ~ v1_relat_1(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).

fof(c_0_31,plain,(
    ! [X16] : k10_relat_1(k1_xboole_0,X16) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t172_relat_1])).

fof(c_0_32,plain,(
    ! [X19,X20,X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))
      | v1_relat_1(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_33,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_34,plain,
    ( esk1_1(k1_tarski(X1)) = X1 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

fof(c_0_35,negated_conjecture,(
    ~ ! [X1] :
        ( l1_orders_2(X1)
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r2_lattice3(X1,k1_xboole_0,X2)
              & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t6_yellow_0])).

cnf(c_0_36,plain,
    ( ~ r2_hidden(X1,k2_relat_1(X2))
    | k10_relat_1(X2,k1_tarski(X1)) != k1_xboole_0
    | ~ v1_relat_1(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_37,plain,
    ( k10_relat_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_38,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[t60_relat_1])).

cnf(c_0_39,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_40,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_22]),c_0_34]),c_0_29])).

fof(c_0_41,plain,(
    ! [X26,X27,X28,X29] :
      ( ( ~ r1_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X29,u1_struct_0(X26))
        | ~ r2_hidden(X29,X27)
        | r1_orders_2(X26,X28,X29)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( m1_subset_1(esk2_3(X26,X27,X28),u1_struct_0(X26))
        | r1_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( r2_hidden(esk2_3(X26,X27,X28),X27)
        | r1_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) )
      & ( ~ r1_orders_2(X26,X28,esk2_3(X26,X27,X28))
        | r1_lattice3(X26,X27,X28)
        | ~ m1_subset_1(X28,u1_struct_0(X26))
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).

fof(c_0_42,negated_conjecture,
    ( l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & ( ~ r2_lattice3(esk4_0,k1_xboole_0,esk5_0)
      | ~ r1_lattice3(esk4_0,k1_xboole_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).

cnf(c_0_43,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ r2_hidden(X1,k1_xboole_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_38])).

cnf(c_0_44,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_45,plain,
    ( r2_hidden(esk2_3(X1,X2,X3),X2)
    | r1_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_47,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_48,plain,(
    ! [X31,X32,X33,X34] :
      ( ( ~ r2_lattice3(X31,X32,X33)
        | ~ m1_subset_1(X34,u1_struct_0(X31))
        | ~ r2_hidden(X34,X32)
        | r1_orders_2(X31,X34,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( m1_subset_1(esk3_3(X31,X32,X33),u1_struct_0(X31))
        | r2_lattice3(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( r2_hidden(esk3_3(X31,X32,X33),X32)
        | r2_lattice3(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( ~ r1_orders_2(X31,esk3_3(X31,X32,X33),X33)
        | r2_lattice3(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).

cnf(c_0_49,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43,c_0_44])])).

cnf(c_0_50,negated_conjecture,
    ( r1_lattice3(esk4_0,X1,esk5_0)
    | r2_hidden(esk2_3(esk4_0,X1,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])])).

cnf(c_0_51,plain,
    ( r2_hidden(esk3_3(X1,X2,X3),X2)
    | r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_52,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,k1_xboole_0,esk5_0)
    | ~ r1_lattice3(esk4_0,k1_xboole_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_53,negated_conjecture,
    ( r1_lattice3(esk4_0,k1_xboole_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( r2_lattice3(esk4_0,X1,esk5_0)
    | r2_hidden(esk3_3(esk4_0,X1,esk5_0),X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_46]),c_0_47])])).

cnf(c_0_55,negated_conjecture,
    ( ~ r2_lattice3(esk4_0,k1_xboole_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53])])).

cnf(c_0_56,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_54]),c_0_55]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:02:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.19/0.39  # and selection function PSelectComplexPreferEQ.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.044 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(l35_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 0.19/0.39  fof(t9_mcart_1, axiom, ![X1]:~((X1!=k1_xboole_0&![X2]:~((r2_hidden(X2,X1)&![X3, X4]:~(((r2_hidden(X3,X1)|r2_hidden(X4,X1))&X2=k4_tarski(X3,X4))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_mcart_1)).
% 0.19/0.39  fof(t49_zfmisc_1, axiom, ![X1, X2]:k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 0.19/0.39  fof(t1_boole, axiom, ![X1]:k2_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 0.19/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.39  fof(t61_setfam_1, axiom, ![X1]:m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_setfam_1)).
% 0.19/0.39  fof(t21_zfmisc_1, axiom, ![X1, X2]:(k4_xboole_0(k1_tarski(X1),k1_tarski(X2))=k1_xboole_0=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 0.19/0.39  fof(t142_funct_1, axiom, ![X1, X2]:(v1_relat_1(X2)=>(r2_hidden(X1,k2_relat_1(X2))<=>k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_1)).
% 0.19/0.39  fof(t172_relat_1, axiom, ![X1]:k10_relat_1(k1_xboole_0,X1)=k1_xboole_0, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 0.19/0.39  fof(cc1_relset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))=>v1_relat_1(X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 0.19/0.39  fof(t6_yellow_0, conjecture, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_yellow_0)).
% 0.19/0.39  fof(t60_relat_1, axiom, (k1_relat_1(k1_xboole_0)=k1_xboole_0&k2_relat_1(k1_xboole_0)=k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 0.19/0.39  fof(d8_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X3,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_lattice3)).
% 0.19/0.39  fof(d9_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_lattice3(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(r2_hidden(X4,X2)=>r1_orders_2(X1,X4,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_lattice3)).
% 0.19/0.39  fof(c_0_14, plain, ![X6, X7]:((k4_xboole_0(k1_tarski(X6),X7)!=k1_xboole_0|r2_hidden(X6,X7))&(~r2_hidden(X6,X7)|k4_xboole_0(k1_tarski(X6),X7)=k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l35_zfmisc_1])])).
% 0.19/0.39  fof(c_0_15, plain, ![X22, X24, X25]:((r2_hidden(esk1_1(X22),X22)|X22=k1_xboole_0)&((~r2_hidden(X24,X22)|esk1_1(X22)!=k4_tarski(X24,X25)|X22=k1_xboole_0)&(~r2_hidden(X25,X22)|esk1_1(X22)!=k4_tarski(X24,X25)|X22=k1_xboole_0))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t9_mcart_1])])])])])).
% 0.19/0.39  fof(c_0_16, plain, ![X10, X11]:k2_xboole_0(k1_tarski(X10),X11)!=k1_xboole_0, inference(variable_rename,[status(thm)],[t49_zfmisc_1])).
% 0.19/0.39  fof(c_0_17, plain, ![X5]:k2_xboole_0(X5,k1_xboole_0)=X5, inference(variable_rename,[status(thm)],[t1_boole])).
% 0.19/0.39  fof(c_0_18, plain, ![X12, X13, X14]:(~r2_hidden(X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(X14))|m1_subset_1(X12,X14)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.39  fof(c_0_19, plain, ![X15]:m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X15))), inference(variable_rename,[status(thm)],[t61_setfam_1])).
% 0.19/0.39  fof(c_0_20, plain, ![X8, X9]:(k4_xboole_0(k1_tarski(X8),k1_tarski(X9))!=k1_xboole_0|X8=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t21_zfmisc_1])])).
% 0.19/0.39  cnf(c_0_21, plain, (k4_xboole_0(k1_tarski(X1),X2)=k1_xboole_0|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.39  cnf(c_0_22, plain, (r2_hidden(esk1_1(X1),X1)|X1=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.39  cnf(c_0_23, plain, (k2_xboole_0(k1_tarski(X1),X2)!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.39  cnf(c_0_24, plain, (k2_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_25, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_26, plain, (m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_27, plain, (X1=X2|k4_xboole_0(k1_tarski(X1),k1_tarski(X2))!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.39  cnf(c_0_28, plain, (k4_xboole_0(k1_tarski(esk1_1(X1)),X1)=k1_xboole_0|X1=k1_xboole_0), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.19/0.39  cnf(c_0_29, plain, (k1_tarski(X1)!=k1_xboole_0), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.39  fof(c_0_30, plain, ![X17, X18]:((~r2_hidden(X17,k2_relat_1(X18))|k10_relat_1(X18,k1_tarski(X17))!=k1_xboole_0|~v1_relat_1(X18))&(k10_relat_1(X18,k1_tarski(X17))=k1_xboole_0|r2_hidden(X17,k2_relat_1(X18))|~v1_relat_1(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t142_funct_1])])])).
% 0.19/0.39  fof(c_0_31, plain, ![X16]:k10_relat_1(k1_xboole_0,X16)=k1_xboole_0, inference(variable_rename,[status(thm)],[t172_relat_1])).
% 0.19/0.39  fof(c_0_32, plain, ![X19, X20, X21]:(~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(X19,X20)))|v1_relat_1(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).
% 0.19/0.39  cnf(c_0_33, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X1,k1_tarski(k1_xboole_0))), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.39  cnf(c_0_34, plain, (esk1_1(k1_tarski(X1))=X1), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_28]), c_0_29])).
% 0.19/0.39  fof(c_0_35, negated_conjecture, ~(![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r2_lattice3(X1,k1_xboole_0,X2)&r1_lattice3(X1,k1_xboole_0,X2))))), inference(assume_negation,[status(cth)],[t6_yellow_0])).
% 0.19/0.39  cnf(c_0_36, plain, (~r2_hidden(X1,k2_relat_1(X2))|k10_relat_1(X2,k1_tarski(X1))!=k1_xboole_0|~v1_relat_1(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  cnf(c_0_37, plain, (k10_relat_1(k1_xboole_0,X1)=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.19/0.39  cnf(c_0_38, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(split_conjunct,[status(thm)],[t60_relat_1])).
% 0.19/0.39  cnf(c_0_39, plain, (v1_relat_1(X1)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.19/0.39  cnf(c_0_40, plain, (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1))), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_22]), c_0_34]), c_0_29])).
% 0.19/0.39  fof(c_0_41, plain, ![X26, X27, X28, X29]:((~r1_lattice3(X26,X27,X28)|(~m1_subset_1(X29,u1_struct_0(X26))|(~r2_hidden(X29,X27)|r1_orders_2(X26,X28,X29)))|~m1_subset_1(X28,u1_struct_0(X26))|~l1_orders_2(X26))&((m1_subset_1(esk2_3(X26,X27,X28),u1_struct_0(X26))|r1_lattice3(X26,X27,X28)|~m1_subset_1(X28,u1_struct_0(X26))|~l1_orders_2(X26))&((r2_hidden(esk2_3(X26,X27,X28),X27)|r1_lattice3(X26,X27,X28)|~m1_subset_1(X28,u1_struct_0(X26))|~l1_orders_2(X26))&(~r1_orders_2(X26,X28,esk2_3(X26,X27,X28))|r1_lattice3(X26,X27,X28)|~m1_subset_1(X28,u1_struct_0(X26))|~l1_orders_2(X26))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_lattice3])])])])])).
% 0.19/0.39  fof(c_0_42, negated_conjecture, (l1_orders_2(esk4_0)&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(~r2_lattice3(esk4_0,k1_xboole_0,esk5_0)|~r1_lattice3(esk4_0,k1_xboole_0,esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_35])])])).
% 0.19/0.39  cnf(c_0_43, plain, (~v1_relat_1(k1_xboole_0)|~r2_hidden(X1,k1_xboole_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_38])).
% 0.19/0.39  cnf(c_0_44, plain, (v1_relat_1(k1_xboole_0)), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 0.19/0.39  cnf(c_0_45, plain, (r2_hidden(esk2_3(X1,X2,X3),X2)|r1_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.39  cnf(c_0_46, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_47, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  fof(c_0_48, plain, ![X31, X32, X33, X34]:((~r2_lattice3(X31,X32,X33)|(~m1_subset_1(X34,u1_struct_0(X31))|(~r2_hidden(X34,X32)|r1_orders_2(X31,X34,X33)))|~m1_subset_1(X33,u1_struct_0(X31))|~l1_orders_2(X31))&((m1_subset_1(esk3_3(X31,X32,X33),u1_struct_0(X31))|r2_lattice3(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~l1_orders_2(X31))&((r2_hidden(esk3_3(X31,X32,X33),X32)|r2_lattice3(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~l1_orders_2(X31))&(~r1_orders_2(X31,esk3_3(X31,X32,X33),X33)|r2_lattice3(X31,X32,X33)|~m1_subset_1(X33,u1_struct_0(X31))|~l1_orders_2(X31))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_lattice3])])])])])).
% 0.19/0.39  cnf(c_0_49, plain, (~r2_hidden(X1,k1_xboole_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_43, c_0_44])])).
% 0.19/0.39  cnf(c_0_50, negated_conjecture, (r1_lattice3(esk4_0,X1,esk5_0)|r2_hidden(esk2_3(esk4_0,X1,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_47])])).
% 0.19/0.39  cnf(c_0_51, plain, (r2_hidden(esk3_3(X1,X2,X3),X2)|r2_lattice3(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.39  cnf(c_0_52, negated_conjecture, (~r2_lattice3(esk4_0,k1_xboole_0,esk5_0)|~r1_lattice3(esk4_0,k1_xboole_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (r1_lattice3(esk4_0,k1_xboole_0,esk5_0)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.39  cnf(c_0_54, negated_conjecture, (r2_lattice3(esk4_0,X1,esk5_0)|r2_hidden(esk3_3(esk4_0,X1,esk5_0),X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_46]), c_0_47])])).
% 0.19/0.39  cnf(c_0_55, negated_conjecture, (~r2_lattice3(esk4_0,k1_xboole_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_52, c_0_53])])).
% 0.19/0.39  cnf(c_0_56, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_54]), c_0_55]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 57
% 0.19/0.39  # Proof object clause steps            : 29
% 0.19/0.39  # Proof object formula steps           : 28
% 0.19/0.39  # Proof object conjectures             : 11
% 0.19/0.39  # Proof object clause conjectures      : 8
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 16
% 0.19/0.39  # Proof object initial formulas used   : 14
% 0.19/0.39  # Proof object generating inferences   : 11
% 0.19/0.39  # Proof object simplifying inferences  : 13
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 15
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 28
% 0.19/0.39  # Removed in clause preprocessing      : 0
% 0.19/0.39  # Initial clauses in saturation        : 28
% 0.19/0.39  # Processed clauses                    : 91
% 0.19/0.39  # ...of these trivial                  : 3
% 0.19/0.39  # ...subsumed                          : 5
% 0.19/0.39  # ...remaining for further processing  : 83
% 0.19/0.39  # Other redundant clauses eliminated   : 2
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 0
% 0.19/0.39  # Backward-rewritten                   : 3
% 0.19/0.39  # Generated clauses                    : 55
% 0.19/0.39  # ...of the previous two non-trivial   : 50
% 0.19/0.39  # Contextual simplify-reflections      : 0
% 0.19/0.39  # Paramodulations                      : 53
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 2
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 52
% 0.19/0.39  #    Positive orientable unit clauses  : 16
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 6
% 0.19/0.39  #    Non-unit-clauses                  : 30
% 0.19/0.39  # Current number of unprocessed clauses: 12
% 0.19/0.39  # ...number of literals in the above   : 35
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 31
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 92
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 64
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 3
% 0.19/0.39  # Unit Clause-clause subsumption calls : 24
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 3
% 0.19/0.39  # BW rewrite match successes           : 2
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 2942
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.051 s
% 0.19/0.39  # System time              : 0.003 s
% 0.19/0.39  # Total time               : 0.054 s
% 0.19/0.39  # Maximum resident set size: 1584 pages
%------------------------------------------------------------------------------
