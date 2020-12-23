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
% DateTime   : Thu Dec  3 11:09:46 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 150 expanded)
%              Number of clauses        :   24 (  48 expanded)
%              Number of leaves         :    5 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  187 (1082 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t49_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ~ ( r2_hidden(X2,X3)
                  & r2_hidden(X2,k2_orders_2(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

fof(fraenkel_a_2_1_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_1_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X4,X5) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d13_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(irreflexivity_r2_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ~ r2_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r2_hidden(X2,X3)
                    & r2_hidden(X2,k2_orders_2(X1,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t49_orders_2])).

fof(c_0_6,plain,(
    ! [X11,X12,X13,X15,X16] :
      ( ( m1_subset_1(esk1_3(X11,X12,X13),u1_struct_0(X12))
        | ~ r2_hidden(X11,a_2_1_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( X11 = esk1_3(X11,X12,X13)
        | ~ r2_hidden(X11,a_2_1_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X15,X13)
        | r2_orders_2(X12,esk1_3(X11,X12,X13),X15)
        | ~ r2_hidden(X11,a_2_1_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( m1_subset_1(esk2_4(X11,X12,X13,X16),u1_struct_0(X12))
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | X11 != X16
        | r2_hidden(X11,a_2_1_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( r2_hidden(esk2_4(X11,X12,X13,X16),X13)
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | X11 != X16
        | r2_hidden(X11,a_2_1_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( ~ r2_orders_2(X12,X16,esk2_4(X11,X12,X13,X16))
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | X11 != X16
        | r2_hidden(X11,a_2_1_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).

fof(c_0_7,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | m1_subset_1(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_8,plain,(
    ! [X9,X10] :
      ( v2_struct_0(X9)
      | ~ v3_orders_2(X9)
      | ~ v4_orders_2(X9)
      | ~ v5_orders_2(X9)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | k2_orders_2(X9,X10) = a_2_1_orders_2(X9,X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).

fof(c_0_9,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & r2_hidden(esk4_0,esk5_0)
    & r2_hidden(esk4_0,k2_orders_2(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_10,plain,
    ( r2_orders_2(X2,esk1_3(X4,X2,X3),X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | k2_orders_2(X1,X2) = a_2_1_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_17,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_19,plain,
    ( r2_orders_2(X1,esk1_3(X2,X1,X3),X4)
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X2,a_2_1_orders_2(X1,X3))
    | ~ r2_hidden(X4,X3) ),
    inference(csr,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_20,plain,
    ( X1 = esk1_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_21,negated_conjecture,
    ( r2_hidden(esk4_0,k2_orders_2(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_22,negated_conjecture,
    ( k2_orders_2(esk3_0,esk5_0) = a_2_1_orders_2(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

fof(c_0_23,plain,(
    ! [X18,X19,X20] :
      ( ~ l1_orders_2(X18)
      | ~ m1_subset_1(X19,u1_struct_0(X18))
      | ~ m1_subset_1(X20,u1_struct_0(X18))
      | ~ r2_orders_2(X18,X19,X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_orders_2])])])).

cnf(c_0_24,negated_conjecture,
    ( r2_orders_2(esk3_0,esk1_3(X1,esk3_0,esk5_0),X2)
    | ~ r2_hidden(X1,a_2_1_orders_2(esk3_0,esk5_0))
    | ~ r2_hidden(X2,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_26,negated_conjecture,
    ( esk1_3(X1,esk3_0,esk5_0) = X1
    | ~ r2_hidden(X1,a_2_1_orders_2(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(esk4_0,a_2_1_orders_2(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_28,plain,
    ( ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_orders_2(X1,X2,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( r2_orders_2(esk3_0,esk1_3(X1,esk3_0,esk5_0),esk4_0)
    | ~ r2_hidden(X1,a_2_1_orders_2(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( esk1_3(esk4_0,esk3_0,esk5_0) = esk4_0 ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( ~ r2_orders_2(esk3_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_14])])).

cnf(c_0_33,negated_conjecture,
    ( r2_orders_2(esk3_0,esk4_0,esk4_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_27]),c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:12:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.35  # No SInE strategy applied
% 0.12/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.20/0.39  # and selection function SelectNewComplexAHP.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.041 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t49_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r2_hidden(X2,X3)&r2_hidden(X2,k2_orders_2(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_orders_2)).
% 0.20/0.39  fof(fraenkel_a_2_1_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_1_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X4,X5)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_1_orders_2)).
% 0.20/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.20/0.39  fof(d13_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d13_orders_2)).
% 0.20/0.39  fof(irreflexivity_r2_orders_2, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>~(r2_orders_2(X1,X2,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', irreflexivity_r2_orders_2)).
% 0.20/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r2_hidden(X2,X3)&r2_hidden(X2,k2_orders_2(X1,X3)))))))), inference(assume_negation,[status(cth)],[t49_orders_2])).
% 0.20/0.39  fof(c_0_6, plain, ![X11, X12, X13, X15, X16]:((((m1_subset_1(esk1_3(X11,X12,X13),u1_struct_0(X12))|~r2_hidden(X11,a_2_1_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))&(X11=esk1_3(X11,X12,X13)|~r2_hidden(X11,a_2_1_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))))&(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_hidden(X15,X13)|r2_orders_2(X12,esk1_3(X11,X12,X13),X15))|~r2_hidden(X11,a_2_1_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))))&((m1_subset_1(esk2_4(X11,X12,X13,X16),u1_struct_0(X12))|(~m1_subset_1(X16,u1_struct_0(X12))|X11!=X16)|r2_hidden(X11,a_2_1_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))&((r2_hidden(esk2_4(X11,X12,X13,X16),X13)|(~m1_subset_1(X16,u1_struct_0(X12))|X11!=X16)|r2_hidden(X11,a_2_1_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))&(~r2_orders_2(X12,X16,esk2_4(X11,X12,X13,X16))|(~m1_subset_1(X16,u1_struct_0(X12))|X11!=X16)|r2_hidden(X11,a_2_1_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_1_orders_2])])])])])])).
% 0.20/0.39  fof(c_0_7, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|m1_subset_1(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.20/0.39  fof(c_0_8, plain, ![X9, X10]:(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|k2_orders_2(X9,X10)=a_2_1_orders_2(X9,X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d13_orders_2])])])])).
% 0.20/0.39  fof(c_0_9, negated_conjecture, (((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(r2_hidden(esk4_0,esk5_0)&r2_hidden(esk4_0,k2_orders_2(esk3_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.20/0.39  cnf(c_0_10, plain, (r2_orders_2(X2,esk1_3(X4,X2,X3),X1)|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  cnf(c_0_11, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.39  cnf(c_0_12, plain, (v2_struct_0(X1)|k2_orders_2(X1,X2)=a_2_1_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.39  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_14, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_16, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_19, plain, (r2_orders_2(X1,esk1_3(X2,X1,X3),X4)|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X2,a_2_1_orders_2(X1,X3))|~r2_hidden(X4,X3)), inference(csr,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.39  cnf(c_0_20, plain, (X1=esk1_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_1_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.39  cnf(c_0_21, negated_conjecture, (r2_hidden(esk4_0,k2_orders_2(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (k2_orders_2(esk3_0,esk5_0)=a_2_1_orders_2(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.39  fof(c_0_23, plain, ![X18, X19, X20]:(~l1_orders_2(X18)|~m1_subset_1(X19,u1_struct_0(X18))|~m1_subset_1(X20,u1_struct_0(X18))|~r2_orders_2(X18,X19,X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[irreflexivity_r2_orders_2])])])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (r2_orders_2(esk3_0,esk1_3(X1,esk3_0,esk5_0),X2)|~r2_hidden(X1,a_2_1_orders_2(esk3_0,esk5_0))|~r2_hidden(X2,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (esk1_3(X1,esk3_0,esk5_0)=X1|~r2_hidden(X1,a_2_1_orders_2(esk3_0,esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.39  cnf(c_0_27, negated_conjecture, (r2_hidden(esk4_0,a_2_1_orders_2(esk3_0,esk5_0))), inference(rw,[status(thm)],[c_0_21, c_0_22])).
% 0.20/0.39  cnf(c_0_28, plain, (~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_orders_2(X1,X2,X2)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.39  cnf(c_0_30, negated_conjecture, (r2_orders_2(esk3_0,esk1_3(X1,esk3_0,esk5_0),esk4_0)|~r2_hidden(X1,a_2_1_orders_2(esk3_0,esk5_0))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.20/0.39  cnf(c_0_31, negated_conjecture, (esk1_3(esk4_0,esk3_0,esk5_0)=esk4_0), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (~r2_orders_2(esk3_0,X1,X1)|~m1_subset_1(X1,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_14])])).
% 0.20/0.39  cnf(c_0_33, negated_conjecture, (r2_orders_2(esk3_0,esk4_0,esk4_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_27]), c_0_31])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_29])]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 35
% 0.20/0.39  # Proof object clause steps            : 24
% 0.20/0.39  # Proof object formula steps           : 11
% 0.20/0.39  # Proof object conjectures             : 21
% 0.20/0.39  # Proof object clause conjectures      : 18
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 14
% 0.20/0.39  # Proof object initial formulas used   : 5
% 0.20/0.39  # Proof object generating inferences   : 8
% 0.20/0.39  # Proof object simplifying inferences  : 25
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 5
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 18
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 18
% 0.20/0.39  # Processed clauses                    : 52
% 0.20/0.39  # ...of these trivial                  : 1
% 0.20/0.39  # ...subsumed                          : 0
% 0.20/0.39  # ...remaining for further processing  : 51
% 0.20/0.39  # Other redundant clauses eliminated   : 3
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 0
% 0.20/0.39  # Backward-rewritten                   : 1
% 0.20/0.39  # Generated clauses                    : 20
% 0.20/0.39  # ...of the previous two non-trivial   : 16
% 0.20/0.39  # Contextual simplify-reflections      : 1
% 0.20/0.39  # Paramodulations                      : 17
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 3
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
% 0.20/0.39  # Current number of processed clauses  : 29
% 0.20/0.39  #    Positive orientable unit clauses  : 11
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 1
% 0.20/0.39  #    Non-unit-clauses                  : 17
% 0.20/0.39  # Current number of unprocessed clauses: 0
% 0.20/0.39  # ...number of literals in the above   : 0
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 19
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 177
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 32
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.20/0.39  # Unit Clause-clause subsumption calls : 7
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 2
% 0.20/0.39  # BW rewrite match successes           : 1
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 2523
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.047 s
% 0.20/0.39  # System time              : 0.003 s
% 0.20/0.39  # Total time               : 0.050 s
% 0.20/0.39  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
