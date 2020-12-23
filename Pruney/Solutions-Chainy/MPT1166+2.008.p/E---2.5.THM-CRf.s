%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:10:01 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 124 expanded)
%              Number of clauses        :   28 (  42 expanded)
%              Number of leaves         :    5 (  30 expanded)
%              Depth                    :   11
%              Number of atoms          :  147 ( 846 expanded)
%              Number of equality atoms :   21 (  94 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t69_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ~ ( X2 != k1_xboole_0
                  & m1_orders_2(X2,X1,X3)
                  & m1_orders_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

fof(t67_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_orders_2(X3,X1,X2)
             => r1_tarski(X3,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(d8_xboole_0,axiom,(
    ! [X1,X2] :
      ( r2_xboole_0(X1,X2)
    <=> ( r1_tarski(X1,X2)
        & X1 != X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(t58_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X2,X3) )
     => r2_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

fof(t68_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ~ ( X2 != k1_xboole_0
                & m1_orders_2(X2,X1,X2) )
            & ~ ( ~ m1_orders_2(X2,X1,X2)
                & X2 = k1_xboole_0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( X2 != k1_xboole_0
                    & m1_orders_2(X2,X1,X3)
                    & m1_orders_2(X3,X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t69_orders_2])).

fof(c_0_6,plain,(
    ! [X9,X10,X11] :
      ( v2_struct_0(X9)
      | ~ v3_orders_2(X9)
      | ~ v4_orders_2(X9)
      | ~ v5_orders_2(X9)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ m1_orders_2(X11,X9,X10)
      | r1_tarski(X11,X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & esk2_0 != k1_xboole_0
    & m1_orders_2(esk2_0,esk1_0,esk3_0)
    & m1_orders_2(esk3_0,esk1_0,esk2_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

fof(c_0_8,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | ~ r2_xboole_0(X4,X5) )
      & ( X4 != X5
        | ~ r2_xboole_0(X4,X5) )
      & ( ~ r1_tarski(X4,X5)
        | X4 = X5
        | r2_xboole_0(X4,X5) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).

cnf(c_0_9,plain,
    ( v2_struct_0(X1)
    | r1_tarski(X3,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_orders_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_14,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,plain,
    ( X1 = X2
    | r2_xboole_0(X1,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_17,negated_conjecture,
    ( r1_tarski(X1,esk3_0)
    | ~ m1_orders_2(X1,esk1_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_10]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_18,negated_conjecture,
    ( X1 = esk3_0
    | r2_xboole_0(X1,esk3_0)
    | ~ m1_orders_2(X1,esk1_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_19,negated_conjecture,
    ( m1_orders_2(esk2_0,esk1_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_20,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_xboole_0(X6,X7)
      | ~ r1_tarski(X7,X8)
      | r2_xboole_0(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_xboole_1])])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( esk3_0 = esk2_0
    | r2_xboole_0(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,plain,
    ( X1 != X2
    | ~ r2_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( r2_xboole_0(X1,X3)
    | ~ r2_xboole_0(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( esk3_0 = esk2_0
    | r1_tarski(esk2_0,esk3_0) ),
    inference(spm,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(X1,esk2_0)
    | ~ m1_orders_2(X1,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_23]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_28,plain,
    ( ~ r2_xboole_0(X1,X1) ),
    inference(er,[status(thm)],[c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( esk3_0 = esk2_0
    | r2_xboole_0(X1,esk3_0)
    | ~ r2_xboole_0(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_30,plain,(
    ! [X12,X13] :
      ( ( X13 = k1_xboole_0
        | ~ m1_orders_2(X13,X12,X13)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) )
      & ( m1_orders_2(X13,X12,X13)
        | X13 != k1_xboole_0
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_orders_2])])])])])).

cnf(c_0_31,negated_conjecture,
    ( X1 = esk2_0
    | r2_xboole_0(X1,esk2_0)
    | ~ m1_orders_2(X1,esk1_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_16,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( m1_orders_2(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_33,negated_conjecture,
    ( esk3_0 = esk2_0
    | ~ r2_xboole_0(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,plain,
    ( X1 = k1_xboole_0
    | v2_struct_0(X2)
    | ~ m1_orders_2(X1,X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( esk2_0 != k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_36,negated_conjecture,
    ( esk3_0 = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( ~ m1_orders_2(esk2_0,esk1_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_23]),c_0_11]),c_0_12]),c_0_13]),c_0_14])]),c_0_35]),c_0_15])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_32,c_0_36]),c_0_37]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:11:11 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S021N
% 0.20/0.39  # and selection function PSelectAllCondOptimalLit.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.050 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t69_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X2!=k1_xboole_0&m1_orders_2(X2,X1,X3))&m1_orders_2(X3,X1,X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_orders_2)).
% 0.20/0.39  fof(t67_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_orders_2(X3,X1,X2)=>r1_tarski(X3,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_orders_2)).
% 0.20/0.39  fof(d8_xboole_0, axiom, ![X1, X2]:(r2_xboole_0(X1,X2)<=>(r1_tarski(X1,X2)&X1!=X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 0.20/0.39  fof(t58_xboole_1, axiom, ![X1, X2, X3]:((r2_xboole_0(X1,X2)&r1_tarski(X2,X3))=>r2_xboole_0(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 0.20/0.39  fof(t68_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(~((X2!=k1_xboole_0&m1_orders_2(X2,X1,X2)))&~((~(m1_orders_2(X2,X1,X2))&X2=k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_orders_2)).
% 0.20/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~(((X2!=k1_xboole_0&m1_orders_2(X2,X1,X3))&m1_orders_2(X3,X1,X2))))))), inference(assume_negation,[status(cth)],[t69_orders_2])).
% 0.20/0.39  fof(c_0_6, plain, ![X9, X10, X11]:(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|(~m1_orders_2(X11,X9,X10)|r1_tarski(X11,X10)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t67_orders_2])])])])).
% 0.20/0.39  fof(c_0_7, negated_conjecture, (((((~v2_struct_0(esk1_0)&v3_orders_2(esk1_0))&v4_orders_2(esk1_0))&v5_orders_2(esk1_0))&l1_orders_2(esk1_0))&(m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&(m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))&((esk2_0!=k1_xboole_0&m1_orders_2(esk2_0,esk1_0,esk3_0))&m1_orders_2(esk3_0,esk1_0,esk2_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.20/0.39  fof(c_0_8, plain, ![X4, X5]:(((r1_tarski(X4,X5)|~r2_xboole_0(X4,X5))&(X4!=X5|~r2_xboole_0(X4,X5)))&(~r1_tarski(X4,X5)|X4=X5|r2_xboole_0(X4,X5))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d8_xboole_0])])])).
% 0.20/0.39  cnf(c_0_9, plain, (v2_struct_0(X1)|r1_tarski(X3,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_orders_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_11, negated_conjecture, (l1_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_12, negated_conjecture, (v5_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_13, negated_conjecture, (v4_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_14, negated_conjecture, (v3_orders_2(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_16, plain, (X1=X2|r2_xboole_0(X1,X2)|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (r1_tarski(X1,esk3_0)|~m1_orders_2(X1,esk1_0,esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_10]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (X1=esk3_0|r2_xboole_0(X1,esk3_0)|~m1_orders_2(X1,esk1_0,esk3_0)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.39  cnf(c_0_19, negated_conjecture, (m1_orders_2(esk2_0,esk1_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  fof(c_0_20, plain, ![X6, X7, X8]:(~r2_xboole_0(X6,X7)|~r1_tarski(X7,X8)|r2_xboole_0(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t58_xboole_1])])).
% 0.20/0.39  cnf(c_0_21, plain, (r1_tarski(X1,X2)|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (esk3_0=esk2_0|r2_xboole_0(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.39  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_24, plain, (X1!=X2|~r2_xboole_0(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_25, plain, (r2_xboole_0(X1,X3)|~r2_xboole_0(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (esk3_0=esk2_0|r1_tarski(esk2_0,esk3_0)), inference(spm,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (r1_tarski(X1,esk2_0)|~m1_orders_2(X1,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9, c_0_23]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_15])).
% 0.20/0.39  cnf(c_0_28, plain, (~r2_xboole_0(X1,X1)), inference(er,[status(thm)],[c_0_24])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (esk3_0=esk2_0|r2_xboole_0(X1,esk3_0)|~r2_xboole_0(X1,esk2_0)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.20/0.39  fof(c_0_30, plain, ![X12, X13]:((X13=k1_xboole_0|~m1_orders_2(X13,X12,X13)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)))&(m1_orders_2(X13,X12,X13)|X13!=k1_xboole_0|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t68_orders_2])])])])])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (X1=esk2_0|r2_xboole_0(X1,esk2_0)|~m1_orders_2(X1,esk1_0,esk2_0)), inference(spm,[status(thm)],[c_0_16, c_0_27])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (m1_orders_2(esk3_0,esk1_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (esk3_0=esk2_0|~r2_xboole_0(esk3_0,esk2_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.39  cnf(c_0_34, plain, (X1=k1_xboole_0|v2_struct_0(X2)|~m1_orders_2(X1,X2,X1)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (esk2_0!=k1_xboole_0), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (esk3_0=esk2_0), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (~m1_orders_2(esk2_0,esk1_0,esk2_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_23]), c_0_11]), c_0_12]), c_0_13]), c_0_14])]), c_0_35]), c_0_15])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_32, c_0_36]), c_0_37]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 39
% 0.20/0.39  # Proof object clause steps            : 28
% 0.20/0.39  # Proof object formula steps           : 11
% 0.20/0.39  # Proof object conjectures             : 24
% 0.20/0.39  # Proof object clause conjectures      : 21
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 16
% 0.20/0.39  # Proof object initial formulas used   : 5
% 0.20/0.39  # Proof object generating inferences   : 10
% 0.20/0.39  # Proof object simplifying inferences  : 23
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 5
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 17
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 17
% 0.20/0.39  # Processed clauses                    : 48
% 0.20/0.39  # ...of these trivial                  : 0
% 0.20/0.39  # ...subsumed                          : 1
% 0.20/0.39  # ...remaining for further processing  : 47
% 0.20/0.39  # Other redundant clauses eliminated   : 2
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 10
% 0.20/0.39  # Generated clauses                    : 17
% 0.20/0.39  # ...of the previous two non-trivial   : 20
% 0.20/0.39  # Contextual simplify-reflections      : 1
% 0.20/0.39  # Paramodulations                      : 15
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 2
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 18
% 0.20/0.39  #    Positive orientable unit clauses  : 6
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 4
% 0.20/0.39  #    Non-unit-clauses                  : 8
% 0.20/0.39  # Current number of unprocessed clauses: 3
% 0.20/0.39  # ...number of literals in the above   : 9
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 27
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 76
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 17
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 2
% 0.20/0.39  # Unit Clause-clause subsumption calls : 7
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 1
% 0.20/0.39  # BW rewrite match successes           : 1
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 1575
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.051 s
% 0.20/0.39  # System time              : 0.006 s
% 0.20/0.39  # Total time               : 0.057 s
% 0.20/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
