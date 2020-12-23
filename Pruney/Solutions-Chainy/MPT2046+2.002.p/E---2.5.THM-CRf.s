%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:50 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   33 ( 190 expanded)
%              Number of clauses        :   22 (  62 expanded)
%              Number of leaves         :    5 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  157 ( 854 expanded)
%              Number of equality atoms :    8 (  20 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   23 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_yellow19,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r2_waybel_7(X1,k1_yellow19(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_yellow19)).

fof(d1_yellow19,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => k1_yellow19(X1,X2) = a_2_0_yellow19(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_yellow19)).

fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(d5_waybel_7,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2,X3] :
          ( r2_waybel_7(X1,X2,X3)
        <=> ! [X4] :
              ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_pre_topc(X4,X1)
                  & r2_hidden(X3,X4) )
               => r2_hidden(X4,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_waybel_7)).

fof(fraenkel_a_2_0_yellow19,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(X1,a_2_0_yellow19(X2,X3))
      <=> ? [X4] :
            ( m1_connsp_2(X4,X2,X3)
            & X1 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_yellow19)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => r2_waybel_7(X1,k1_yellow19(X1,X2),X2) ) ) ),
    inference(assume_negation,[status(cth)],[t5_yellow19])).

fof(c_0_6,plain,(
    ! [X15,X16] :
      ( v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_subset_1(X16,u1_struct_0(X15))
      | k1_yellow19(X15,X16) = a_2_0_yellow19(X15,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_yellow19])])])])).

fof(c_0_7,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,u1_struct_0(esk3_0))
    & ~ r2_waybel_7(esk3_0,k1_yellow19(esk3_0,esk4_0),esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).

cnf(c_0_8,plain,
    ( v2_struct_0(X1)
    | k1_yellow19(X1,X2) = a_2_0_yellow19(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_11,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_13,plain,(
    ! [X5,X6,X7] :
      ( v2_struct_0(X5)
      | ~ v2_pre_topc(X5)
      | ~ l1_pre_topc(X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ v3_pre_topc(X6,X5)
      | ~ r2_hidden(X7,X6)
      | m1_connsp_2(X6,X5,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

cnf(c_0_14,negated_conjecture,
    ( ~ r2_waybel_7(esk3_0,k1_yellow19(esk3_0,esk4_0),esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( k1_yellow19(esk3_0,esk4_0) = a_2_0_yellow19(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11])]),c_0_12])).

fof(c_0_16,plain,(
    ! [X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_waybel_7(X8,X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ v3_pre_topc(X11,X8)
        | ~ r2_hidden(X10,X11)
        | r2_hidden(X11,X9)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( m1_subset_1(esk1_3(X8,X12,X13),k1_zfmisc_1(u1_struct_0(X8)))
        | r2_waybel_7(X8,X12,X13)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( v3_pre_topc(esk1_3(X8,X12,X13),X8)
        | r2_waybel_7(X8,X12,X13)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( r2_hidden(X13,esk1_3(X8,X12,X13))
        | r2_waybel_7(X8,X12,X13)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) )
      & ( ~ r2_hidden(esk1_3(X8,X12,X13),X12)
        | r2_waybel_7(X8,X12,X13)
        | ~ v2_pre_topc(X8)
        | ~ l1_pre_topc(X8) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_7])])])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( ~ r2_waybel_7(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_19,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( r2_hidden(X1,esk1_3(X2,X3,X1))
    | r2_waybel_7(X2,X3,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X17,X18,X19,X21] :
      ( ( m1_connsp_2(esk2_3(X17,X18,X19),X18,X19)
        | ~ r2_hidden(X17,a_2_0_yellow19(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18)) )
      & ( X17 = esk2_3(X17,X18,X19)
        | ~ r2_hidden(X17,a_2_0_yellow19(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18)) )
      & ( ~ m1_connsp_2(X21,X18,X19)
        | X17 != X21
        | r2_hidden(X17,a_2_0_yellow19(X18,X19))
        | v2_struct_0(X18)
        | ~ v2_pre_topc(X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,u1_struct_0(X18)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_yellow19])])])])])])).

cnf(c_0_22,negated_conjecture,
    ( m1_connsp_2(X1,esk3_0,esk4_0)
    | ~ r2_hidden(esk4_0,X1)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_9]),c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_10]),c_0_11])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk4_0,esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_20]),c_0_10]),c_0_11])])).

cnf(c_0_25,plain,
    ( r2_hidden(X4,a_2_0_yellow19(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | X4 != X1
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_connsp_2(esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0),esk3_0,esk4_0)
    | ~ v3_pre_topc(esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0),esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_27,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | r2_waybel_7(X1,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,plain,
    ( r2_hidden(X1,a_2_0_yellow19(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(er,[status(thm)],[c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( m1_connsp_2(esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0),esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_10]),c_0_11])]),c_0_18])).

cnf(c_0_30,plain,
    ( r2_waybel_7(X1,X2,X3)
    | ~ r2_hidden(esk1_3(X1,X2,X3),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( r2_hidden(esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0),a_2_0_yellow19(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_9]),c_0_10]),c_0_11])]),c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_10]),c_0_11])]),c_0_18]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:34:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.13/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S088I
% 0.13/0.38  # and selection function SelectCQArNTEqFirstUnlessPDom.
% 0.13/0.38  #
% 0.13/0.38  # Preprocessing time       : 0.028 s
% 0.13/0.38  # Presaturation interreduction done
% 0.13/0.38  
% 0.13/0.38  # Proof found!
% 0.13/0.38  # SZS status Theorem
% 0.13/0.38  # SZS output start CNFRefutation
% 0.13/0.38  fof(t5_yellow19, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r2_waybel_7(X1,k1_yellow19(X1,X2),X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_yellow19)).
% 0.13/0.38  fof(d1_yellow19, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>k1_yellow19(X1,X2)=a_2_0_yellow19(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_yellow19)).
% 0.13/0.38  fof(t5_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>((v3_pre_topc(X2,X1)&r2_hidden(X3,X2))=>m1_connsp_2(X2,X1,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 0.13/0.38  fof(d5_waybel_7, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2, X3]:(r2_waybel_7(X1,X2,X3)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>((v3_pre_topc(X4,X1)&r2_hidden(X3,X4))=>r2_hidden(X4,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_waybel_7)).
% 0.13/0.38  fof(fraenkel_a_2_0_yellow19, axiom, ![X1, X2, X3]:((((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))&m1_subset_1(X3,u1_struct_0(X2)))=>(r2_hidden(X1,a_2_0_yellow19(X2,X3))<=>?[X4]:(m1_connsp_2(X4,X2,X3)&X1=X4))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fraenkel_a_2_0_yellow19)).
% 0.13/0.38  fof(c_0_5, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r2_waybel_7(X1,k1_yellow19(X1,X2),X2)))), inference(assume_negation,[status(cth)],[t5_yellow19])).
% 0.13/0.38  fof(c_0_6, plain, ![X15, X16]:(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_subset_1(X16,u1_struct_0(X15))|k1_yellow19(X15,X16)=a_2_0_yellow19(X15,X16))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_yellow19])])])])).
% 0.13/0.38  fof(c_0_7, negated_conjecture, (((~v2_struct_0(esk3_0)&v2_pre_topc(esk3_0))&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,u1_struct_0(esk3_0))&~r2_waybel_7(esk3_0,k1_yellow19(esk3_0,esk4_0),esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_5])])])])).
% 0.13/0.38  cnf(c_0_8, plain, (v2_struct_0(X1)|k1_yellow19(X1,X2)=a_2_0_yellow19(X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.13/0.38  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk4_0,u1_struct_0(esk3_0))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_10, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_11, negated_conjecture, (v2_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_12, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  fof(c_0_13, plain, ![X5, X6, X7]:(v2_struct_0(X5)|~v2_pre_topc(X5)|~l1_pre_topc(X5)|(~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))|(~m1_subset_1(X7,u1_struct_0(X5))|(~v3_pre_topc(X6,X5)|~r2_hidden(X7,X6)|m1_connsp_2(X6,X5,X7))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).
% 0.13/0.38  cnf(c_0_14, negated_conjecture, (~r2_waybel_7(esk3_0,k1_yellow19(esk3_0,esk4_0),esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.38  cnf(c_0_15, negated_conjecture, (k1_yellow19(esk3_0,esk4_0)=a_2_0_yellow19(esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11])]), c_0_12])).
% 0.13/0.38  fof(c_0_16, plain, ![X8, X9, X10, X11, X12, X13]:((~r2_waybel_7(X8,X9,X10)|(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X8)))|(~v3_pre_topc(X11,X8)|~r2_hidden(X10,X11)|r2_hidden(X11,X9)))|(~v2_pre_topc(X8)|~l1_pre_topc(X8)))&((m1_subset_1(esk1_3(X8,X12,X13),k1_zfmisc_1(u1_struct_0(X8)))|r2_waybel_7(X8,X12,X13)|(~v2_pre_topc(X8)|~l1_pre_topc(X8)))&(((v3_pre_topc(esk1_3(X8,X12,X13),X8)|r2_waybel_7(X8,X12,X13)|(~v2_pre_topc(X8)|~l1_pre_topc(X8)))&(r2_hidden(X13,esk1_3(X8,X12,X13))|r2_waybel_7(X8,X12,X13)|(~v2_pre_topc(X8)|~l1_pre_topc(X8))))&(~r2_hidden(esk1_3(X8,X12,X13),X12)|r2_waybel_7(X8,X12,X13)|(~v2_pre_topc(X8)|~l1_pre_topc(X8)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_waybel_7])])])])])])).
% 0.13/0.38  cnf(c_0_17, plain, (v2_struct_0(X1)|m1_connsp_2(X2,X1,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))|~v3_pre_topc(X2,X1)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.13/0.38  cnf(c_0_18, negated_conjecture, (~r2_waybel_7(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0)), inference(rw,[status(thm)],[c_0_14, c_0_15])).
% 0.13/0.38  cnf(c_0_19, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|r2_waybel_7(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_20, plain, (r2_hidden(X1,esk1_3(X2,X3,X1))|r2_waybel_7(X2,X3,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  fof(c_0_21, plain, ![X17, X18, X19, X21]:(((m1_connsp_2(esk2_3(X17,X18,X19),X18,X19)|~r2_hidden(X17,a_2_0_yellow19(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18))))&(X17=esk2_3(X17,X18,X19)|~r2_hidden(X17,a_2_0_yellow19(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18)))))&(~m1_connsp_2(X21,X18,X19)|X17!=X21|r2_hidden(X17,a_2_0_yellow19(X18,X19))|(v2_struct_0(X18)|~v2_pre_topc(X18)|~l1_pre_topc(X18)|~m1_subset_1(X19,u1_struct_0(X18))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_yellow19])])])])])])).
% 0.13/0.38  cnf(c_0_22, negated_conjecture, (m1_connsp_2(X1,esk3_0,esk4_0)|~r2_hidden(esk4_0,X1)|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_9]), c_0_10]), c_0_11])]), c_0_12])).
% 0.13/0.38  cnf(c_0_23, negated_conjecture, (m1_subset_1(esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_19]), c_0_10]), c_0_11])])).
% 0.13/0.38  cnf(c_0_24, negated_conjecture, (r2_hidden(esk4_0,esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18, c_0_20]), c_0_10]), c_0_11])])).
% 0.13/0.38  cnf(c_0_25, plain, (r2_hidden(X4,a_2_0_yellow19(X2,X3))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|X4!=X1|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.38  cnf(c_0_26, negated_conjecture, (m1_connsp_2(esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0),esk3_0,esk4_0)|~v3_pre_topc(esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0),esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.13/0.38  cnf(c_0_27, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X1)|r2_waybel_7(X1,X2,X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_28, plain, (r2_hidden(X1,a_2_0_yellow19(X2,X3))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X3,u1_struct_0(X2))|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(er,[status(thm)],[c_0_25])).
% 0.13/0.38  cnf(c_0_29, negated_conjecture, (m1_connsp_2(esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0),esk3_0,esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_10]), c_0_11])]), c_0_18])).
% 0.13/0.38  cnf(c_0_30, plain, (r2_waybel_7(X1,X2,X3)|~r2_hidden(esk1_3(X1,X2,X3),X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.13/0.38  cnf(c_0_31, negated_conjecture, (r2_hidden(esk1_3(esk3_0,a_2_0_yellow19(esk3_0,esk4_0),esk4_0),a_2_0_yellow19(esk3_0,esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_9]), c_0_10]), c_0_11])]), c_0_12])).
% 0.13/0.38  cnf(c_0_32, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_10]), c_0_11])]), c_0_18]), ['proof']).
% 0.13/0.38  # SZS output end CNFRefutation
% 0.13/0.38  # Proof object total steps             : 33
% 0.13/0.38  # Proof object clause steps            : 22
% 0.13/0.38  # Proof object formula steps           : 11
% 0.13/0.38  # Proof object conjectures             : 17
% 0.13/0.38  # Proof object clause conjectures      : 14
% 0.13/0.38  # Proof object formula conjectures     : 3
% 0.13/0.38  # Proof object initial clauses used    : 12
% 0.13/0.38  # Proof object initial formulas used   : 5
% 0.13/0.38  # Proof object generating inferences   : 8
% 0.13/0.38  # Proof object simplifying inferences  : 31
% 0.13/0.38  # Training examples: 0 positive, 0 negative
% 0.13/0.38  # Parsed axioms                        : 5
% 0.13/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.38  # Initial clauses                      : 15
% 0.13/0.38  # Removed in clause preprocessing      : 0
% 0.13/0.38  # Initial clauses in saturation        : 15
% 0.13/0.38  # Processed clauses                    : 40
% 0.13/0.38  # ...of these trivial                  : 0
% 0.13/0.38  # ...subsumed                          : 0
% 0.13/0.38  # ...remaining for further processing  : 40
% 0.13/0.38  # Other redundant clauses eliminated   : 1
% 0.13/0.38  # Clauses deleted for lack of memory   : 0
% 0.13/0.38  # Backward-subsumed                    : 0
% 0.13/0.38  # Backward-rewritten                   : 2
% 0.13/0.38  # Generated clauses                    : 14
% 0.13/0.38  # ...of the previous two non-trivial   : 14
% 0.13/0.38  # Contextual simplify-reflections      : 0
% 0.13/0.38  # Paramodulations                      : 13
% 0.13/0.38  # Factorizations                       : 0
% 0.13/0.38  # Equation resolutions                 : 1
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
% 0.13/0.38  # Current number of processed clauses  : 22
% 0.13/0.38  #    Positive orientable unit clauses  : 8
% 0.13/0.38  #    Positive unorientable unit clauses: 0
% 0.13/0.38  #    Negative unit clauses             : 2
% 0.13/0.38  #    Non-unit-clauses                  : 12
% 0.13/0.38  # Current number of unprocessed clauses: 3
% 0.13/0.38  # ...number of literals in the above   : 16
% 0.13/0.38  # Current number of archived formulas  : 0
% 0.13/0.38  # Current number of archived clauses   : 17
% 0.13/0.38  # Clause-clause subsumption calls (NU) : 54
% 0.13/0.38  # Rec. Clause-clause subsumption calls : 7
% 0.13/0.38  # Non-unit clause-clause subsumptions  : 0
% 0.13/0.38  # Unit Clause-clause subsumption calls : 0
% 0.13/0.38  # Rewrite failures with RHS unbound    : 0
% 0.13/0.38  # BW rewrite match attempts            : 2
% 0.13/0.38  # BW rewrite match successes           : 2
% 0.13/0.38  # Condensation attempts                : 0
% 0.13/0.38  # Condensation successes               : 0
% 0.13/0.38  # Termbank termtop insertions          : 1984
% 0.13/0.38  
% 0.13/0.38  # -------------------------------------------------
% 0.13/0.38  # User time                : 0.030 s
% 0.13/0.38  # System time              : 0.003 s
% 0.13/0.38  # Total time               : 0.033 s
% 0.13/0.38  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
