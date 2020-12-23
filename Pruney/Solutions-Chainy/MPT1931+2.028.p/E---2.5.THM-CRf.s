%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:15 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   41 (  95 expanded)
%              Number of clauses        :   22 (  34 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  188 ( 467 expanded)
%              Number of equality atoms :   11 (  22 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal clause size      :   35 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t10_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ~ r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(redefinition_k6_subset_1,axiom,(
    ! [X1,X2] : k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(t29_yellow_6,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_orders_2(X2)
            & v7_waybel_0(X2)
            & l1_waybel_0(X2,X1) )
         => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(t3_boole,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(t72_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( k4_xboole_0(k2_tarski(X1,X2),X3) = k2_tarski(X1,X2)
    <=> ( ~ r2_hidden(X1,X3)
        & ~ r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(d12_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3] :
              ( r2_waybel_0(X1,X2,X3)
            <=> ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ? [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                      & r1_orders_2(X2,X4,X5)
                      & r2_hidden(k2_waybel_0(X1,X2,X5),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

fof(t8_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_waybel_0(X2,X1) )
         => ! [X3,X4] :
              ( r1_tarski(X3,X4)
             => ( ( r1_waybel_0(X1,X2,X3)
                 => r1_waybel_0(X1,X2,X4) )
                & ( r2_waybel_0(X1,X2,X3)
                 => r2_waybel_0(X1,X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_0)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(c_0_9,plain,(
    ! [X28,X29,X30] :
      ( ( ~ r2_waybel_0(X28,X29,X30)
        | ~ r1_waybel_0(X28,X29,k6_subset_1(u1_struct_0(X28),X30))
        | v2_struct_0(X29)
        | ~ l1_waybel_0(X29,X28)
        | v2_struct_0(X28)
        | ~ l1_struct_0(X28) )
      & ( r1_waybel_0(X28,X29,k6_subset_1(u1_struct_0(X28),X30))
        | r2_waybel_0(X28,X29,X30)
        | v2_struct_0(X29)
        | ~ l1_waybel_0(X29,X28)
        | v2_struct_0(X28)
        | ~ l1_struct_0(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).

fof(c_0_10,plain,(
    ! [X18,X19] : k6_subset_1(X18,X19) = k4_xboole_0(X18,X19) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_struct_0(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_orders_2(X2)
              & v7_waybel_0(X2)
              & l1_waybel_0(X2,X1) )
           => r1_waybel_0(X1,X2,u1_struct_0(X1)) ) ) ),
    inference(assume_negation,[status(cth)],[t29_yellow_6])).

cnf(c_0_12,plain,
    ( r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))
    | r2_waybel_0(X1,X2,X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_13,plain,
    ( k6_subset_1(X1,X2) = k4_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_14,plain,(
    ! [X12] : k4_xboole_0(X12,k1_xboole_0) = X12 ),
    inference(variable_rename,[status(thm)],[t3_boole])).

fof(c_0_15,plain,(
    ! [X13,X14,X15] :
      ( ( ~ r2_hidden(X13,X15)
        | k4_xboole_0(k2_tarski(X13,X14),X15) != k2_tarski(X13,X14) )
      & ( ~ r2_hidden(X14,X15)
        | k4_xboole_0(k2_tarski(X13,X14),X15) != k2_tarski(X13,X14) )
      & ( r2_hidden(X13,X15)
        | r2_hidden(X14,X15)
        | k4_xboole_0(k2_tarski(X13,X14),X15) = k2_tarski(X13,X14) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & l1_struct_0(esk5_0)
    & ~ v2_struct_0(esk6_0)
    & v4_orders_2(esk6_0)
    & v7_waybel_0(esk6_0)
    & l1_waybel_0(esk6_0,esk5_0)
    & ~ r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X2)
    | v2_struct_0(X1)
    | r2_waybel_0(X1,X2,X3)
    | r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))
    | ~ l1_struct_0(X1)
    | ~ l1_waybel_0(X2,X1) ),
    inference(rw,[status(thm)],[c_0_12,c_0_13])).

cnf(c_0_18,plain,
    ( k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( ~ r2_hidden(X1,X2)
    | k4_xboole_0(k2_tarski(X3,X1),X2) != k2_tarski(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X6,X7,X8,X9,X10] :
      ( ( ~ r1_tarski(X6,X7)
        | ~ r2_hidden(X8,X6)
        | r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_2(X9,X10),X9)
        | r1_tarski(X9,X10) )
      & ( ~ r2_hidden(esk1_2(X9,X10),X10)
        | r1_tarski(X9,X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_21,plain,(
    ! [X20,X21,X22,X23,X25,X27] :
      ( ( m1_subset_1(esk3_4(X20,X21,X22,X23),u1_struct_0(X21))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ r2_waybel_0(X20,X21,X22)
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( r1_orders_2(X21,X23,esk3_4(X20,X21,X22,X23))
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ r2_waybel_0(X20,X21,X22)
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( r2_hidden(k2_waybel_0(X20,X21,esk3_4(X20,X21,X22,X23)),X22)
        | ~ m1_subset_1(X23,u1_struct_0(X21))
        | ~ r2_waybel_0(X20,X21,X22)
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( m1_subset_1(esk4_3(X20,X21,X25),u1_struct_0(X21))
        | r2_waybel_0(X20,X21,X25)
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X21))
        | ~ r1_orders_2(X21,esk4_3(X20,X21,X25),X27)
        | ~ r2_hidden(k2_waybel_0(X20,X21,X27),X25)
        | r2_waybel_0(X20,X21,X25)
        | v2_struct_0(X21)
        | ~ l1_waybel_0(X21,X20)
        | v2_struct_0(X20)
        | ~ l1_struct_0(X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).

fof(c_0_22,plain,(
    ! [X31,X32,X33,X34] :
      ( ( ~ r1_waybel_0(X31,X32,X33)
        | r1_waybel_0(X31,X32,X34)
        | ~ r1_tarski(X33,X34)
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31) )
      & ( ~ r2_waybel_0(X31,X32,X33)
        | r2_waybel_0(X31,X32,X34)
        | ~ r1_tarski(X33,X34)
        | v2_struct_0(X32)
        | ~ l1_waybel_0(X32,X31)
        | v2_struct_0(X31)
        | ~ l1_struct_0(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).

cnf(c_0_23,negated_conjecture,
    ( ~ r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( r1_waybel_0(X1,X2,u1_struct_0(X1))
    | r2_waybel_0(X1,X2,k1_xboole_0)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( l1_waybel_0(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,k1_xboole_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_18])).

cnf(c_0_30,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( r2_waybel_0(X1,X2,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ r2_waybel_0(X1,X2,X3)
    | ~ r1_tarski(X3,X4)
    | ~ l1_waybel_0(X2,X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_27]),c_0_28])).

cnf(c_0_34,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ r2_waybel_0(X2,X1,k1_xboole_0)
    | ~ l1_waybel_0(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_31])).

cnf(c_0_36,negated_conjecture,
    ( r2_waybel_0(esk5_0,esk6_0,X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_25]),c_0_26]),c_0_34])]),c_0_28]),c_0_27])).

fof(c_0_37,plain,(
    ! [X16] : m1_subset_1(esk2_1(X16),X16) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_38,negated_conjecture,
    ( ~ m1_subset_1(X1,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_25]),c_0_26])]),c_0_27]),c_0_28])).

cnf(c_0_39,plain,
    ( m1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_40,negated_conjecture,
    ( $false ),
    inference(spm,[status(thm)],[c_0_38,c_0_39]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 09:39:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___300_C18_F1_SE_CS_SP_S0Y
% 0.14/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.029 s
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t10_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>~(r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_waybel_0)).
% 0.14/0.39  fof(redefinition_k6_subset_1, axiom, ![X1, X2]:k6_subset_1(X1,X2)=k4_xboole_0(X1,X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 0.14/0.39  fof(t29_yellow_6, conjecture, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_yellow_6)).
% 0.14/0.39  fof(t3_boole, axiom, ![X1]:k4_xboole_0(X1,k1_xboole_0)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 0.14/0.39  fof(t72_zfmisc_1, axiom, ![X1, X2, X3]:(k4_xboole_0(k2_tarski(X1,X2),X3)=k2_tarski(X1,X2)<=>(~(r2_hidden(X1,X3))&~(r2_hidden(X2,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 0.14/0.39  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.14/0.39  fof(d12_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3]:(r2_waybel_0(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,u1_struct_0(X2))=>?[X5]:((m1_subset_1(X5,u1_struct_0(X2))&r1_orders_2(X2,X4,X5))&r2_hidden(k2_waybel_0(X1,X2,X5),X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_waybel_0)).
% 0.14/0.39  fof(t8_waybel_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((~(v2_struct_0(X2))&l1_waybel_0(X2,X1))=>![X3, X4]:(r1_tarski(X3,X4)=>((r1_waybel_0(X1,X2,X3)=>r1_waybel_0(X1,X2,X4))&(r2_waybel_0(X1,X2,X3)=>r2_waybel_0(X1,X2,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_0)).
% 0.14/0.39  fof(existence_m1_subset_1, axiom, ![X1]:?[X2]:m1_subset_1(X2,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 0.14/0.39  fof(c_0_9, plain, ![X28, X29, X30]:((~r2_waybel_0(X28,X29,X30)|~r1_waybel_0(X28,X29,k6_subset_1(u1_struct_0(X28),X30))|(v2_struct_0(X29)|~l1_waybel_0(X29,X28))|(v2_struct_0(X28)|~l1_struct_0(X28)))&(r1_waybel_0(X28,X29,k6_subset_1(u1_struct_0(X28),X30))|r2_waybel_0(X28,X29,X30)|(v2_struct_0(X29)|~l1_waybel_0(X29,X28))|(v2_struct_0(X28)|~l1_struct_0(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t10_waybel_0])])])])])).
% 0.14/0.39  fof(c_0_10, plain, ![X18, X19]:k6_subset_1(X18,X19)=k4_xboole_0(X18,X19), inference(variable_rename,[status(thm)],[redefinition_k6_subset_1])).
% 0.14/0.39  fof(c_0_11, negated_conjecture, ~(![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>![X2]:((((~(v2_struct_0(X2))&v4_orders_2(X2))&v7_waybel_0(X2))&l1_waybel_0(X2,X1))=>r1_waybel_0(X1,X2,u1_struct_0(X1))))), inference(assume_negation,[status(cth)],[t29_yellow_6])).
% 0.14/0.39  cnf(c_0_12, plain, (r1_waybel_0(X1,X2,k6_subset_1(u1_struct_0(X1),X3))|r2_waybel_0(X1,X2,X3)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.14/0.39  cnf(c_0_13, plain, (k6_subset_1(X1,X2)=k4_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.39  fof(c_0_14, plain, ![X12]:k4_xboole_0(X12,k1_xboole_0)=X12, inference(variable_rename,[status(thm)],[t3_boole])).
% 0.14/0.39  fof(c_0_15, plain, ![X13, X14, X15]:(((~r2_hidden(X13,X15)|k4_xboole_0(k2_tarski(X13,X14),X15)!=k2_tarski(X13,X14))&(~r2_hidden(X14,X15)|k4_xboole_0(k2_tarski(X13,X14),X15)!=k2_tarski(X13,X14)))&(r2_hidden(X13,X15)|r2_hidden(X14,X15)|k4_xboole_0(k2_tarski(X13,X14),X15)=k2_tarski(X13,X14))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t72_zfmisc_1])])])])).
% 0.14/0.39  fof(c_0_16, negated_conjecture, ((~v2_struct_0(esk5_0)&l1_struct_0(esk5_0))&((((~v2_struct_0(esk6_0)&v4_orders_2(esk6_0))&v7_waybel_0(esk6_0))&l1_waybel_0(esk6_0,esk5_0))&~r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0)))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.14/0.39  cnf(c_0_17, plain, (v2_struct_0(X2)|v2_struct_0(X1)|r2_waybel_0(X1,X2,X3)|r1_waybel_0(X1,X2,k4_xboole_0(u1_struct_0(X1),X3))|~l1_struct_0(X1)|~l1_waybel_0(X2,X1)), inference(rw,[status(thm)],[c_0_12, c_0_13])).
% 0.14/0.39  cnf(c_0_18, plain, (k4_xboole_0(X1,k1_xboole_0)=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.14/0.39  cnf(c_0_19, plain, (~r2_hidden(X1,X2)|k4_xboole_0(k2_tarski(X3,X1),X2)!=k2_tarski(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.39  fof(c_0_20, plain, ![X6, X7, X8, X9, X10]:((~r1_tarski(X6,X7)|(~r2_hidden(X8,X6)|r2_hidden(X8,X7)))&((r2_hidden(esk1_2(X9,X10),X9)|r1_tarski(X9,X10))&(~r2_hidden(esk1_2(X9,X10),X10)|r1_tarski(X9,X10)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.14/0.39  fof(c_0_21, plain, ![X20, X21, X22, X23, X25, X27]:((((m1_subset_1(esk3_4(X20,X21,X22,X23),u1_struct_0(X21))|~m1_subset_1(X23,u1_struct_0(X21))|~r2_waybel_0(X20,X21,X22)|(v2_struct_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~l1_struct_0(X20)))&(r1_orders_2(X21,X23,esk3_4(X20,X21,X22,X23))|~m1_subset_1(X23,u1_struct_0(X21))|~r2_waybel_0(X20,X21,X22)|(v2_struct_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~l1_struct_0(X20))))&(r2_hidden(k2_waybel_0(X20,X21,esk3_4(X20,X21,X22,X23)),X22)|~m1_subset_1(X23,u1_struct_0(X21))|~r2_waybel_0(X20,X21,X22)|(v2_struct_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~l1_struct_0(X20))))&((m1_subset_1(esk4_3(X20,X21,X25),u1_struct_0(X21))|r2_waybel_0(X20,X21,X25)|(v2_struct_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~l1_struct_0(X20)))&(~m1_subset_1(X27,u1_struct_0(X21))|~r1_orders_2(X21,esk4_3(X20,X21,X25),X27)|~r2_hidden(k2_waybel_0(X20,X21,X27),X25)|r2_waybel_0(X20,X21,X25)|(v2_struct_0(X21)|~l1_waybel_0(X21,X20))|(v2_struct_0(X20)|~l1_struct_0(X20))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_waybel_0])])])])])])])).
% 0.14/0.39  fof(c_0_22, plain, ![X31, X32, X33, X34]:((~r1_waybel_0(X31,X32,X33)|r1_waybel_0(X31,X32,X34)|~r1_tarski(X33,X34)|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~l1_struct_0(X31)))&(~r2_waybel_0(X31,X32,X33)|r2_waybel_0(X31,X32,X34)|~r1_tarski(X33,X34)|(v2_struct_0(X32)|~l1_waybel_0(X32,X31))|(v2_struct_0(X31)|~l1_struct_0(X31)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t8_waybel_0])])])])])).
% 0.14/0.39  cnf(c_0_23, negated_conjecture, (~r1_waybel_0(esk5_0,esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_24, plain, (r1_waybel_0(X1,X2,u1_struct_0(X1))|r2_waybel_0(X1,X2,k1_xboole_0)|v2_struct_0(X2)|v2_struct_0(X1)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.39  cnf(c_0_25, negated_conjecture, (l1_waybel_0(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_26, negated_conjecture, (l1_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_27, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.39  cnf(c_0_29, plain, (~r2_hidden(X1,k1_xboole_0)), inference(spm,[status(thm)],[c_0_19, c_0_18])).
% 0.14/0.39  cnf(c_0_30, plain, (r2_hidden(esk1_2(X1,X2),X1)|r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.39  cnf(c_0_31, plain, (r2_hidden(k2_waybel_0(X1,X2,esk3_4(X1,X2,X3,X4)),X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_subset_1(X4,u1_struct_0(X2))|~r2_waybel_0(X1,X2,X3)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.39  cnf(c_0_32, plain, (r2_waybel_0(X1,X2,X4)|v2_struct_0(X2)|v2_struct_0(X1)|~r2_waybel_0(X1,X2,X3)|~r1_tarski(X3,X4)|~l1_waybel_0(X2,X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.14/0.39  cnf(c_0_33, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_25]), c_0_26])]), c_0_27]), c_0_28])).
% 0.14/0.39  cnf(c_0_34, plain, (r1_tarski(k1_xboole_0,X1)), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.14/0.39  cnf(c_0_35, plain, (v2_struct_0(X1)|v2_struct_0(X2)|~r2_waybel_0(X2,X1,k1_xboole_0)|~l1_waybel_0(X1,X2)|~l1_struct_0(X2)|~m1_subset_1(X3,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_29, c_0_31])).
% 0.14/0.39  cnf(c_0_36, negated_conjecture, (r2_waybel_0(esk5_0,esk6_0,X1)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_25]), c_0_26]), c_0_34])]), c_0_28]), c_0_27])).
% 0.14/0.39  fof(c_0_37, plain, ![X16]:m1_subset_1(esk2_1(X16),X16), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).
% 0.14/0.39  cnf(c_0_38, negated_conjecture, (~m1_subset_1(X1,u1_struct_0(esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_25]), c_0_26])]), c_0_27]), c_0_28])).
% 0.14/0.39  cnf(c_0_39, plain, (m1_subset_1(esk2_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.39  cnf(c_0_40, negated_conjecture, ($false), inference(spm,[status(thm)],[c_0_38, c_0_39]), ['proof']).
% 0.14/0.39  # SZS output end CNFRefutation
% 0.14/0.39  # Proof object total steps             : 41
% 0.14/0.39  # Proof object clause steps            : 22
% 0.14/0.39  # Proof object formula steps           : 19
% 0.14/0.39  # Proof object conjectures             : 12
% 0.14/0.39  # Proof object clause conjectures      : 9
% 0.14/0.39  # Proof object formula conjectures     : 3
% 0.14/0.39  # Proof object initial clauses used    : 13
% 0.14/0.39  # Proof object initial formulas used   : 9
% 0.14/0.39  # Proof object generating inferences   : 8
% 0.14/0.39  # Proof object simplifying inferences  : 17
% 0.14/0.39  # Training examples: 0 positive, 0 negative
% 0.14/0.39  # Parsed axioms                        : 9
% 0.14/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.39  # Initial clauses                      : 25
% 0.14/0.39  # Removed in clause preprocessing      : 1
% 0.14/0.39  # Initial clauses in saturation        : 24
% 0.14/0.39  # Processed clauses                    : 40
% 0.14/0.39  # ...of these trivial                  : 0
% 0.14/0.39  # ...subsumed                          : 5
% 0.14/0.39  # ...remaining for further processing  : 35
% 0.14/0.39  # Other redundant clauses eliminated   : 0
% 0.14/0.39  # Clauses deleted for lack of memory   : 0
% 0.14/0.39  # Backward-subsumed                    : 0
% 0.14/0.39  # Backward-rewritten                   : 1
% 0.14/0.39  # Generated clauses                    : 26
% 0.14/0.39  # ...of the previous two non-trivial   : 19
% 0.14/0.39  # Contextual simplify-reflections      : 0
% 0.14/0.39  # Paramodulations                      : 26
% 0.14/0.39  # Factorizations                       : 0
% 0.14/0.39  # Equation resolutions                 : 0
% 0.14/0.39  # Propositional unsat checks           : 0
% 0.14/0.39  #    Propositional check models        : 0
% 0.14/0.39  #    Propositional check unsatisfiable : 0
% 0.14/0.39  #    Propositional clauses             : 0
% 0.14/0.39  #    Propositional clauses after purity: 0
% 0.14/0.39  #    Propositional unsat core size     : 0
% 0.14/0.39  #    Propositional preprocessing time  : 0.000
% 0.14/0.39  #    Propositional encoding time       : 0.000
% 0.14/0.39  #    Propositional solver time         : 0.000
% 0.14/0.39  #    Success case prop preproc time    : 0.000
% 0.14/0.39  #    Success case prop encoding time   : 0.000
% 0.14/0.39  #    Success case prop solver time     : 0.000
% 0.14/0.39  # Current number of processed clauses  : 34
% 0.14/0.39  #    Positive orientable unit clauses  : 9
% 0.14/0.39  #    Positive unorientable unit clauses: 0
% 0.14/0.39  #    Negative unit clauses             : 5
% 0.14/0.39  #    Non-unit-clauses                  : 20
% 0.14/0.39  # Current number of unprocessed clauses: 1
% 0.14/0.39  # ...number of literals in the above   : 12
% 0.14/0.39  # Current number of archived formulas  : 0
% 0.14/0.39  # Current number of archived clauses   : 2
% 0.14/0.39  # Clause-clause subsumption calls (NU) : 153
% 0.14/0.39  # Rec. Clause-clause subsumption calls : 7
% 0.14/0.39  # Non-unit clause-clause subsumptions  : 3
% 0.14/0.39  # Unit Clause-clause subsumption calls : 3
% 0.14/0.39  # Rewrite failures with RHS unbound    : 0
% 0.14/0.39  # BW rewrite match attempts            : 4
% 0.14/0.39  # BW rewrite match successes           : 1
% 0.14/0.39  # Condensation attempts                : 0
% 0.14/0.39  # Condensation successes               : 0
% 0.14/0.39  # Termbank termtop insertions          : 2506
% 0.14/0.39  
% 0.14/0.39  # -------------------------------------------------
% 0.14/0.39  # User time                : 0.030 s
% 0.14/0.39  # System time              : 0.005 s
% 0.14/0.39  # Total time               : 0.035 s
% 0.14/0.39  # Maximum resident set size: 1580 pages
%------------------------------------------------------------------------------
