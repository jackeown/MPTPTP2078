%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:41 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 ( 145 expanded)
%              Number of clauses        :   21 (  45 expanded)
%              Number of leaves         :    4 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :  184 (1079 expanded)
%              Number of equality atoms :   15 (  24 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   56 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t47_orders_2,conjecture,(
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
                  & r2_hidden(X2,k1_orders_2(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

fof(d12_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(fraenkel_a_2_0_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X5,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(d10_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> ( r1_orders_2(X1,X2,X3)
                  & X2 != X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_orders_2)).

fof(c_0_4,negated_conjecture,(
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
                    & r2_hidden(X2,k1_orders_2(X1,X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t47_orders_2])).

fof(c_0_5,plain,(
    ! [X9,X10] :
      ( v2_struct_0(X9)
      | ~ v3_orders_2(X9)
      | ~ v4_orders_2(X9)
      | ~ v5_orders_2(X9)
      | ~ l1_orders_2(X9)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
      | k1_orders_2(X9,X10) = a_2_0_orders_2(X9,X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

fof(c_0_6,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v3_orders_2(esk3_0)
    & v4_orders_2(esk3_0)
    & v5_orders_2(esk3_0)
    & l1_orders_2(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & r2_hidden(esk4_0,esk5_0)
    & r2_hidden(esk4_0,k1_orders_2(esk3_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X15,X16] :
      ( ( m1_subset_1(esk1_3(X11,X12,X13),u1_struct_0(X12))
        | ~ r2_hidden(X11,a_2_0_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( X11 = esk1_3(X11,X12,X13)
        | ~ r2_hidden(X11,a_2_0_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( ~ m1_subset_1(X15,u1_struct_0(X12))
        | ~ r2_hidden(X15,X13)
        | r2_orders_2(X12,X15,esk1_3(X11,X12,X13))
        | ~ r2_hidden(X11,a_2_0_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( m1_subset_1(esk2_4(X11,X12,X13,X16),u1_struct_0(X12))
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | X11 != X16
        | r2_hidden(X11,a_2_0_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( r2_hidden(esk2_4(X11,X12,X13,X16),X13)
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | X11 != X16
        | r2_hidden(X11,a_2_0_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) )
      & ( ~ r2_orders_2(X12,esk2_4(X11,X12,X13,X16),X16)
        | ~ m1_subset_1(X16,u1_struct_0(X12))
        | X11 != X16
        | r2_hidden(X11,a_2_0_orders_2(X12,X13))
        | v2_struct_0(X12)
        | ~ v3_orders_2(X12)
        | ~ v4_orders_2(X12)
        | ~ v5_orders_2(X12)
        | ~ l1_orders_2(X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

cnf(c_0_8,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( v5_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( v4_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( v3_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( l1_orders_2(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_15,plain,(
    ! [X6,X7,X8] :
      ( ( r1_orders_2(X6,X7,X8)
        | ~ r2_orders_2(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ l1_orders_2(X6) )
      & ( X7 != X8
        | ~ r2_orders_2(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ l1_orders_2(X6) )
      & ( ~ r1_orders_2(X6,X7,X8)
        | X7 = X8
        | r2_orders_2(X6,X7,X8)
        | ~ m1_subset_1(X8,u1_struct_0(X6))
        | ~ m1_subset_1(X7,u1_struct_0(X6))
        | ~ l1_orders_2(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).

cnf(c_0_16,plain,
    ( r2_orders_2(X2,X1,esk1_3(X4,X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_18,negated_conjecture,
    ( r2_hidden(esk4_0,k1_orders_2(esk3_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,negated_conjecture,
    ( k1_orders_2(esk3_0,esk5_0) = a_2_0_orders_2(esk3_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_20,plain,
    ( X1 != X2
    | ~ r2_orders_2(X3,X1,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( r2_orders_2(esk3_0,esk4_0,esk1_3(X1,esk3_0,X2))
    | ~ r2_hidden(X1,a_2_0_orders_2(esk3_0,X2))
    | ~ r2_hidden(esk4_0,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16,c_0_17]),c_0_10]),c_0_11]),c_0_12]),c_0_13])]),c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_23,plain,
    ( X1 = esk1_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_0,a_2_0_orders_2(esk3_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_25,plain,
    ( ~ r2_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(er,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( r2_orders_2(esk3_0,esk4_0,esk1_3(X1,esk3_0,esk5_0))
    | ~ r2_hidden(X1,a_2_0_orders_2(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_22]),c_0_9])])).

cnf(c_0_27,negated_conjecture,
    ( esk1_3(esk4_0,esk3_0,esk5_0) = esk4_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_10]),c_0_11]),c_0_12]),c_0_9]),c_0_13])]),c_0_14])).

cnf(c_0_28,negated_conjecture,
    ( ~ r2_orders_2(esk3_0,esk4_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_17]),c_0_13])])).

cnf(c_0_29,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_24]),c_0_27]),c_0_28]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:53:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.37  # AutoSched0-Mode selected heuristic G_E___207_C18_F1_SE_CS_SP_PI_PS_S2SI
% 0.21/0.37  # and selection function SelectNewComplexAHP.
% 0.21/0.37  #
% 0.21/0.37  # Preprocessing time       : 0.027 s
% 0.21/0.37  # Presaturation interreduction done
% 0.21/0.37  
% 0.21/0.37  # Proof found!
% 0.21/0.37  # SZS status Theorem
% 0.21/0.37  # SZS output start CNFRefutation
% 0.21/0.37  fof(t47_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r2_hidden(X2,X3)&r2_hidden(X2,k1_orders_2(X1,X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_orders_2)).
% 0.21/0.37  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d12_orders_2)).
% 0.21/0.37  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 0.21/0.37  fof(d10_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>(r1_orders_2(X1,X2,X3)&X2!=X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_orders_2)).
% 0.21/0.37  fof(c_0_4, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r2_hidden(X2,X3)&r2_hidden(X2,k1_orders_2(X1,X3)))))))), inference(assume_negation,[status(cth)],[t47_orders_2])).
% 0.21/0.37  fof(c_0_5, plain, ![X9, X10]:(v2_struct_0(X9)|~v3_orders_2(X9)|~v4_orders_2(X9)|~v5_orders_2(X9)|~l1_orders_2(X9)|(~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))|k1_orders_2(X9,X10)=a_2_0_orders_2(X9,X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 0.21/0.37  fof(c_0_6, negated_conjecture, (((((~v2_struct_0(esk3_0)&v3_orders_2(esk3_0))&v4_orders_2(esk3_0))&v5_orders_2(esk3_0))&l1_orders_2(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(r2_hidden(esk4_0,esk5_0)&r2_hidden(esk4_0,k1_orders_2(esk3_0,esk5_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_4])])])])).
% 0.21/0.37  fof(c_0_7, plain, ![X11, X12, X13, X15, X16]:((((m1_subset_1(esk1_3(X11,X12,X13),u1_struct_0(X12))|~r2_hidden(X11,a_2_0_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))&(X11=esk1_3(X11,X12,X13)|~r2_hidden(X11,a_2_0_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))))&(~m1_subset_1(X15,u1_struct_0(X12))|(~r2_hidden(X15,X13)|r2_orders_2(X12,X15,esk1_3(X11,X12,X13)))|~r2_hidden(X11,a_2_0_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12))))))&((m1_subset_1(esk2_4(X11,X12,X13,X16),u1_struct_0(X12))|(~m1_subset_1(X16,u1_struct_0(X12))|X11!=X16)|r2_hidden(X11,a_2_0_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))&((r2_hidden(esk2_4(X11,X12,X13,X16),X13)|(~m1_subset_1(X16,u1_struct_0(X12))|X11!=X16)|r2_hidden(X11,a_2_0_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))&(~r2_orders_2(X12,esk2_4(X11,X12,X13,X16),X16)|(~m1_subset_1(X16,u1_struct_0(X12))|X11!=X16)|r2_hidden(X11,a_2_0_orders_2(X12,X13))|(v2_struct_0(X12)|~v3_orders_2(X12)|~v4_orders_2(X12)|~v5_orders_2(X12)|~l1_orders_2(X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 0.21/0.37  cnf(c_0_8, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_5])).
% 0.21/0.37  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_10, negated_conjecture, (v5_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_11, negated_conjecture, (v4_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_12, negated_conjecture, (v3_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_13, negated_conjecture, (l1_orders_2(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_14, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  fof(c_0_15, plain, ![X6, X7, X8]:(((r1_orders_2(X6,X7,X8)|~r2_orders_2(X6,X7,X8)|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|~l1_orders_2(X6))&(X7!=X8|~r2_orders_2(X6,X7,X8)|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|~l1_orders_2(X6)))&(~r1_orders_2(X6,X7,X8)|X7=X8|r2_orders_2(X6,X7,X8)|~m1_subset_1(X8,u1_struct_0(X6))|~m1_subset_1(X7,u1_struct_0(X6))|~l1_orders_2(X6))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_orders_2])])])])).
% 0.21/0.37  cnf(c_0_16, plain, (r2_orders_2(X2,X1,esk1_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.37  cnf(c_0_17, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_18, negated_conjecture, (r2_hidden(esk4_0,k1_orders_2(esk3_0,esk5_0))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_19, negated_conjecture, (k1_orders_2(esk3_0,esk5_0)=a_2_0_orders_2(esk3_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.21/0.37  cnf(c_0_20, plain, (X1!=X2|~r2_orders_2(X3,X1,X2)|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.37  cnf(c_0_21, negated_conjecture, (r2_orders_2(esk3_0,esk4_0,esk1_3(X1,esk3_0,X2))|~r2_hidden(X1,a_2_0_orders_2(esk3_0,X2))|~r2_hidden(esk4_0,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_16, c_0_17]), c_0_10]), c_0_11]), c_0_12]), c_0_13])]), c_0_14])).
% 0.21/0.37  cnf(c_0_22, negated_conjecture, (r2_hidden(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.37  cnf(c_0_23, plain, (X1=esk1_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.37  cnf(c_0_24, negated_conjecture, (r2_hidden(esk4_0,a_2_0_orders_2(esk3_0,esk5_0))), inference(rw,[status(thm)],[c_0_18, c_0_19])).
% 0.21/0.37  cnf(c_0_25, plain, (~r2_orders_2(X1,X2,X2)|~m1_subset_1(X2,u1_struct_0(X1))|~l1_orders_2(X1)), inference(er,[status(thm)],[c_0_20])).
% 0.21/0.37  cnf(c_0_26, negated_conjecture, (r2_orders_2(esk3_0,esk4_0,esk1_3(X1,esk3_0,esk5_0))|~r2_hidden(X1,a_2_0_orders_2(esk3_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21, c_0_22]), c_0_9])])).
% 0.21/0.37  cnf(c_0_27, negated_conjecture, (esk1_3(esk4_0,esk3_0,esk5_0)=esk4_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23, c_0_24]), c_0_10]), c_0_11]), c_0_12]), c_0_9]), c_0_13])]), c_0_14])).
% 0.21/0.37  cnf(c_0_28, negated_conjecture, (~r2_orders_2(esk3_0,esk4_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25, c_0_17]), c_0_13])])).
% 0.21/0.37  cnf(c_0_29, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_24]), c_0_27]), c_0_28]), ['proof']).
% 0.21/0.37  # SZS output end CNFRefutation
% 0.21/0.37  # Proof object total steps             : 30
% 0.21/0.37  # Proof object clause steps            : 21
% 0.21/0.37  # Proof object formula steps           : 9
% 0.21/0.37  # Proof object conjectures             : 19
% 0.21/0.37  # Proof object clause conjectures      : 16
% 0.21/0.37  # Proof object formula conjectures     : 3
% 0.21/0.37  # Proof object initial clauses used    : 13
% 0.21/0.37  # Proof object initial formulas used   : 4
% 0.21/0.37  # Proof object generating inferences   : 6
% 0.21/0.37  # Proof object simplifying inferences  : 27
% 0.21/0.37  # Training examples: 0 positive, 0 negative
% 0.21/0.37  # Parsed axioms                        : 4
% 0.21/0.37  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.37  # Initial clauses                      : 19
% 0.21/0.37  # Removed in clause preprocessing      : 0
% 0.21/0.37  # Initial clauses in saturation        : 19
% 0.21/0.37  # Processed clauses                    : 53
% 0.21/0.37  # ...of these trivial                  : 1
% 0.21/0.37  # ...subsumed                          : 0
% 0.21/0.38  # ...remaining for further processing  : 52
% 0.21/0.38  # Other redundant clauses eliminated   : 4
% 0.21/0.38  # Clauses deleted for lack of memory   : 0
% 0.21/0.38  # Backward-subsumed                    : 0
% 0.21/0.38  # Backward-rewritten                   : 1
% 0.21/0.38  # Generated clauses                    : 19
% 0.21/0.38  # ...of the previous two non-trivial   : 17
% 0.21/0.38  # Contextual simplify-reflections      : 0
% 0.21/0.38  # Paramodulations                      : 15
% 0.21/0.38  # Factorizations                       : 0
% 0.21/0.38  # Equation resolutions                 : 4
% 0.21/0.38  # Propositional unsat checks           : 0
% 0.21/0.38  #    Propositional check models        : 0
% 0.21/0.38  #    Propositional check unsatisfiable : 0
% 0.21/0.38  #    Propositional clauses             : 0
% 0.21/0.38  #    Propositional clauses after purity: 0
% 0.21/0.38  #    Propositional unsat core size     : 0
% 0.21/0.38  #    Propositional preprocessing time  : 0.000
% 0.21/0.38  #    Propositional encoding time       : 0.000
% 0.21/0.38  #    Propositional solver time         : 0.000
% 0.21/0.38  #    Success case prop preproc time    : 0.000
% 0.21/0.38  #    Success case prop encoding time   : 0.000
% 0.21/0.38  #    Success case prop solver time     : 0.000
% 0.21/0.38  # Current number of processed clauses  : 28
% 0.21/0.38  #    Positive orientable unit clauses  : 10
% 0.21/0.38  #    Positive unorientable unit clauses: 0
% 0.21/0.38  #    Negative unit clauses             : 2
% 0.21/0.38  #    Non-unit-clauses                  : 16
% 0.21/0.38  # Current number of unprocessed clauses: 2
% 0.21/0.38  # ...number of literals in the above   : 6
% 0.21/0.38  # Current number of archived formulas  : 0
% 0.21/0.38  # Current number of archived clauses   : 20
% 0.21/0.38  # Clause-clause subsumption calls (NU) : 336
% 0.21/0.38  # Rec. Clause-clause subsumption calls : 9
% 0.21/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.21/0.38  # Unit Clause-clause subsumption calls : 11
% 0.21/0.38  # Rewrite failures with RHS unbound    : 0
% 0.21/0.38  # BW rewrite match attempts            : 1
% 0.21/0.38  # BW rewrite match successes           : 1
% 0.21/0.38  # Condensation attempts                : 0
% 0.21/0.38  # Condensation successes               : 0
% 0.21/0.38  # Termbank termtop insertions          : 2633
% 0.21/0.38  
% 0.21/0.38  # -------------------------------------------------
% 0.21/0.38  # User time                : 0.031 s
% 0.21/0.38  # System time              : 0.003 s
% 0.21/0.38  # Total time               : 0.034 s
% 0.21/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
