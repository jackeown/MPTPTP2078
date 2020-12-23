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
% DateTime   : Thu Dec  3 11:14:17 EST 2020

% Result     : Theorem 0.17s
% Output     : CNFRefutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 296 expanded)
%              Number of clauses        :   32 ( 112 expanded)
%              Number of leaves         :    6 (  69 expanded)
%              Depth                    :   14
%              Number of atoms          :  169 (1571 expanded)
%              Number of equality atoms :   15 ( 187 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_compts_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( X3 = X4
                   => ( v2_compts_1(X3,X1)
                    <=> v2_compts_1(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).

fof(t11_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X3,k2_struct_0(X2))
               => ( v2_compts_1(X3,X1)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X4 = X3
                       => v2_compts_1(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X3 = X4
                     => ( v2_compts_1(X3,X1)
                      <=> v2_compts_1(X4,X2) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_compts_1])).

fof(c_0_7,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ v2_compts_1(X13,X11)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | X14 != X13
        | v2_compts_1(X14,X12)
        | ~ r1_tarski(X13,k2_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_pre_topc(X12,X11)
        | ~ l1_pre_topc(X11) )
      & ( m1_subset_1(esk1_3(X11,X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v2_compts_1(X13,X11)
        | ~ r1_tarski(X13,k2_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_pre_topc(X12,X11)
        | ~ l1_pre_topc(X11) )
      & ( esk1_3(X11,X12,X13) = X13
        | v2_compts_1(X13,X11)
        | ~ r1_tarski(X13,k2_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_pre_topc(X12,X11)
        | ~ l1_pre_topc(X11) )
      & ( ~ v2_compts_1(esk1_3(X11,X12,X13),X12)
        | v2_compts_1(X13,X11)
        | ~ r1_tarski(X13,k2_struct_0(X12))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ m1_pre_topc(X12,X11)
        | ~ l1_pre_topc(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).

fof(c_0_8,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_pre_topc(esk3_0,esk2_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & esk4_0 = esk5_0
    & ( ~ v2_compts_1(esk4_0,esk2_0)
      | ~ v2_compts_1(esk5_0,esk3_0) )
    & ( v2_compts_1(esk4_0,esk2_0)
      | v2_compts_1(esk5_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( v2_compts_1(X3,X4)
    | ~ v2_compts_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | X3 != X1
    | ~ r1_tarski(X1,k2_struct_0(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_11,negated_conjecture,
    ( esk4_0 = esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_12,plain,(
    ! [X7] :
      ( ~ l1_struct_0(X7)
      | k2_struct_0(X7) = u1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_13,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(X8)
      | l1_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_14,plain,(
    ! [X9,X10] :
      ( ~ l1_pre_topc(X9)
      | ~ m1_pre_topc(X10,X9)
      | l1_pre_topc(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_15,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ r1_tarski(X1,k2_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_9])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_17,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_21,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_22,negated_conjecture,
    ( v2_compts_1(esk4_0,esk3_0)
    | ~ v2_compts_1(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(esk4_0,k2_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

cnf(c_0_23,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

fof(c_0_25,plain,(
    ! [X5,X6] :
      ( ( ~ m1_subset_1(X5,k1_zfmisc_1(X6))
        | r1_tarski(X5,X6) )
      & ( ~ r1_tarski(X5,X6)
        | m1_subset_1(X5,k1_zfmisc_1(X6)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_26,negated_conjecture,
    ( v2_compts_1(esk4_0,esk3_0)
    | ~ v2_compts_1(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ r1_tarski(esk4_0,u1_struct_0(esk3_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( v2_compts_1(esk4_0,esk2_0)
    | v2_compts_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_compts_1(esk4_0,esk2_0)
    | ~ v2_compts_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_30,negated_conjecture,
    ( v2_compts_1(esk4_0,esk3_0)
    | ~ v2_compts_1(esk4_0,X1)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_16])])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_32,negated_conjecture,
    ( v2_compts_1(esk4_0,esk3_0)
    | v2_compts_1(esk4_0,esk2_0) ),
    inference(rw,[status(thm)],[c_0_28,c_0_11])).

cnf(c_0_33,plain,
    ( esk1_3(X1,X2,X3) = X3
    | v2_compts_1(X3,X1)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_compts_1(esk4_0,esk2_0)
    | ~ v2_compts_1(esk4_0,esk3_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_11])).

cnf(c_0_35,negated_conjecture,
    ( v2_compts_1(esk4_0,esk3_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_20]),c_0_21]),c_0_31])]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( esk1_3(esk2_0,X1,esk4_0) = esk4_0
    | v2_compts_1(esk4_0,esk2_0)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ r1_tarski(esk4_0,k2_struct_0(X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_31]),c_0_21])])).

cnf(c_0_37,negated_conjecture,
    ( ~ v2_compts_1(esk4_0,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34,c_0_35])])).

cnf(c_0_38,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_compts_1(esk1_3(X1,X2,X3),X2)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_39,negated_conjecture,
    ( esk1_3(esk2_0,X1,esk4_0) = esk4_0
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_27]),c_0_37])).

cnf(c_0_40,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_compts_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ r1_tarski(esk4_0,k2_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_21]),c_0_31])]),c_0_37]),c_0_40])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_compts_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(k2_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_27])).

cnf(c_0_43,negated_conjecture,
    ( ~ v2_compts_1(esk4_0,X1)
    | ~ m1_pre_topc(X1,esk2_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_42,c_0_23])).

cnf(c_0_44,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_20]),c_0_35]),c_0_24]),c_0_16])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.11/0.32  % Computer   : n019.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % WCLimit    : 600
% 0.11/0.32  % DateTime   : Tue Dec  1 18:28:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  # Version: 2.5pre002
% 0.11/0.33  # No SInE strategy applied
% 0.11/0.33  # Trying AutoSched0 for 299 seconds
% 0.17/0.36  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.17/0.36  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.17/0.36  #
% 0.17/0.36  # Preprocessing time       : 0.031 s
% 0.17/0.36  # Presaturation interreduction done
% 0.17/0.36  
% 0.17/0.36  # Proof found!
% 0.17/0.36  # SZS status Theorem
% 0.17/0.36  # SZS output start CNFRefutation
% 0.17/0.36  fof(t28_compts_1, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X3=X4=>(v2_compts_1(X3,X1)<=>v2_compts_1(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_compts_1)).
% 0.17/0.36  fof(t11_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,k2_struct_0(X2))=>(v2_compts_1(X3,X1)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X4=X3=>v2_compts_1(X4,X2)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_compts_1)).
% 0.17/0.36  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.17/0.36  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.17/0.36  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.17/0.36  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.17/0.36  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X3=X4=>(v2_compts_1(X3,X1)<=>v2_compts_1(X4,X2)))))))), inference(assume_negation,[status(cth)],[t28_compts_1])).
% 0.17/0.36  fof(c_0_7, plain, ![X11, X12, X13, X14]:((~v2_compts_1(X13,X11)|(~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|(X14!=X13|v2_compts_1(X14,X12)))|~r1_tarski(X13,k2_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))|~m1_pre_topc(X12,X11)|~l1_pre_topc(X11))&((m1_subset_1(esk1_3(X11,X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|v2_compts_1(X13,X11)|~r1_tarski(X13,k2_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))|~m1_pre_topc(X12,X11)|~l1_pre_topc(X11))&((esk1_3(X11,X12,X13)=X13|v2_compts_1(X13,X11)|~r1_tarski(X13,k2_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))|~m1_pre_topc(X12,X11)|~l1_pre_topc(X11))&(~v2_compts_1(esk1_3(X11,X12,X13),X12)|v2_compts_1(X13,X11)|~r1_tarski(X13,k2_struct_0(X12))|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X11)))|~m1_pre_topc(X12,X11)|~l1_pre_topc(X11))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).
% 0.17/0.36  fof(c_0_8, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_pre_topc(esk3_0,esk2_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(esk4_0=esk5_0&((~v2_compts_1(esk4_0,esk2_0)|~v2_compts_1(esk5_0,esk3_0))&(v2_compts_1(esk4_0,esk2_0)|v2_compts_1(esk5_0,esk3_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).
% 0.17/0.36  cnf(c_0_9, plain, (v2_compts_1(X3,X4)|~v2_compts_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|X3!=X1|~r1_tarski(X1,k2_struct_0(X4))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X4,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.36  cnf(c_0_10, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.36  cnf(c_0_11, negated_conjecture, (esk4_0=esk5_0), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.36  fof(c_0_12, plain, ![X7]:(~l1_struct_0(X7)|k2_struct_0(X7)=u1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.17/0.36  fof(c_0_13, plain, ![X8]:(~l1_pre_topc(X8)|l1_struct_0(X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.17/0.36  fof(c_0_14, plain, ![X9, X10]:(~l1_pre_topc(X9)|(~m1_pre_topc(X10,X9)|l1_pre_topc(X10))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.17/0.36  cnf(c_0_15, plain, (v2_compts_1(X1,X2)|~v2_compts_1(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~r1_tarski(X1,k2_struct_0(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_9])).
% 0.17/0.36  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_10, c_0_11])).
% 0.17/0.36  cnf(c_0_17, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.17/0.36  cnf(c_0_18, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.17/0.36  cnf(c_0_19, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.17/0.36  cnf(c_0_20, negated_conjecture, (m1_pre_topc(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.36  cnf(c_0_21, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.36  cnf(c_0_22, negated_conjecture, (v2_compts_1(esk4_0,esk3_0)|~v2_compts_1(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~r1_tarski(esk4_0,k2_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.17/0.36  cnf(c_0_23, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.17/0.36  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_20]), c_0_21])])).
% 0.17/0.36  fof(c_0_25, plain, ![X5, X6]:((~m1_subset_1(X5,k1_zfmisc_1(X6))|r1_tarski(X5,X6))&(~r1_tarski(X5,X6)|m1_subset_1(X5,k1_zfmisc_1(X6)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.17/0.36  cnf(c_0_26, negated_conjecture, (v2_compts_1(esk4_0,esk3_0)|~v2_compts_1(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~r1_tarski(esk4_0,u1_struct_0(esk3_0))|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.17/0.36  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.36  cnf(c_0_28, negated_conjecture, (v2_compts_1(esk4_0,esk2_0)|v2_compts_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.36  cnf(c_0_29, negated_conjecture, (~v2_compts_1(esk4_0,esk2_0)|~v2_compts_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.36  cnf(c_0_30, negated_conjecture, (v2_compts_1(esk4_0,esk3_0)|~v2_compts_1(esk4_0,X1)|~m1_pre_topc(esk3_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_16])])).
% 0.17/0.36  cnf(c_0_31, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.17/0.36  cnf(c_0_32, negated_conjecture, (v2_compts_1(esk4_0,esk3_0)|v2_compts_1(esk4_0,esk2_0)), inference(rw,[status(thm)],[c_0_28, c_0_11])).
% 0.17/0.36  cnf(c_0_33, plain, (esk1_3(X1,X2,X3)=X3|v2_compts_1(X3,X1)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.36  cnf(c_0_34, negated_conjecture, (~v2_compts_1(esk4_0,esk2_0)|~v2_compts_1(esk4_0,esk3_0)), inference(rw,[status(thm)],[c_0_29, c_0_11])).
% 0.17/0.36  cnf(c_0_35, negated_conjecture, (v2_compts_1(esk4_0,esk3_0)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_20]), c_0_21]), c_0_31])]), c_0_32])).
% 0.17/0.36  cnf(c_0_36, negated_conjecture, (esk1_3(esk2_0,X1,esk4_0)=esk4_0|v2_compts_1(esk4_0,esk2_0)|~m1_pre_topc(X1,esk2_0)|~r1_tarski(esk4_0,k2_struct_0(X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_31]), c_0_21])])).
% 0.17/0.36  cnf(c_0_37, negated_conjecture, (~v2_compts_1(esk4_0,esk2_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_34, c_0_35])])).
% 0.17/0.36  cnf(c_0_38, plain, (v2_compts_1(X3,X1)|~v2_compts_1(esk1_3(X1,X2,X3),X2)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.17/0.36  cnf(c_0_39, negated_conjecture, (esk1_3(esk2_0,X1,esk4_0)=esk4_0|~m1_pre_topc(X1,esk2_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_struct_0(X1)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_27]), c_0_37])).
% 0.17/0.36  cnf(c_0_40, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.17/0.36  cnf(c_0_41, negated_conjecture, (~v2_compts_1(esk4_0,X1)|~m1_pre_topc(X1,esk2_0)|~r1_tarski(esk4_0,k2_struct_0(X1))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_21]), c_0_31])]), c_0_37]), c_0_40])).
% 0.17/0.36  cnf(c_0_42, negated_conjecture, (~v2_compts_1(esk4_0,X1)|~m1_pre_topc(X1,esk2_0)|~m1_subset_1(esk4_0,k1_zfmisc_1(k2_struct_0(X1)))), inference(spm,[status(thm)],[c_0_41, c_0_27])).
% 0.17/0.36  cnf(c_0_43, negated_conjecture, (~v2_compts_1(esk4_0,X1)|~m1_pre_topc(X1,esk2_0)|~l1_pre_topc(X1)|~m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_42, c_0_23])).
% 0.17/0.36  cnf(c_0_44, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_20]), c_0_35]), c_0_24]), c_0_16])]), ['proof']).
% 0.17/0.36  # SZS output end CNFRefutation
% 0.17/0.36  # Proof object total steps             : 45
% 0.17/0.36  # Proof object clause steps            : 32
% 0.17/0.36  # Proof object formula steps           : 13
% 0.17/0.36  # Proof object conjectures             : 25
% 0.17/0.36  # Proof object clause conjectures      : 22
% 0.17/0.36  # Proof object formula conjectures     : 3
% 0.17/0.36  # Proof object initial clauses used    : 15
% 0.17/0.36  # Proof object initial formulas used   : 6
% 0.17/0.36  # Proof object generating inferences   : 12
% 0.17/0.36  # Proof object simplifying inferences  : 28
% 0.17/0.36  # Training examples: 0 positive, 0 negative
% 0.17/0.36  # Parsed axioms                        : 6
% 0.17/0.36  # Removed by relevancy pruning/SinE    : 0
% 0.17/0.36  # Initial clauses                      : 16
% 0.17/0.36  # Removed in clause preprocessing      : 0
% 0.17/0.36  # Initial clauses in saturation        : 16
% 0.17/0.36  # Processed clauses                    : 49
% 0.17/0.36  # ...of these trivial                  : 0
% 0.17/0.36  # ...subsumed                          : 0
% 0.17/0.36  # ...remaining for further processing  : 49
% 0.17/0.36  # Other redundant clauses eliminated   : 1
% 0.17/0.36  # Clauses deleted for lack of memory   : 0
% 0.17/0.36  # Backward-subsumed                    : 5
% 0.17/0.36  # Backward-rewritten                   : 3
% 0.17/0.36  # Generated clauses                    : 27
% 0.17/0.36  # ...of the previous two non-trivial   : 25
% 0.17/0.36  # Contextual simplify-reflections      : 2
% 0.17/0.36  # Paramodulations                      : 26
% 0.17/0.36  # Factorizations                       : 0
% 0.17/0.36  # Equation resolutions                 : 1
% 0.17/0.36  # Propositional unsat checks           : 0
% 0.17/0.36  #    Propositional check models        : 0
% 0.17/0.36  #    Propositional check unsatisfiable : 0
% 0.17/0.36  #    Propositional clauses             : 0
% 0.17/0.36  #    Propositional clauses after purity: 0
% 0.17/0.36  #    Propositional unsat core size     : 0
% 0.17/0.36  #    Propositional preprocessing time  : 0.000
% 0.17/0.36  #    Propositional encoding time       : 0.000
% 0.17/0.36  #    Propositional solver time         : 0.000
% 0.17/0.36  #    Success case prop preproc time    : 0.000
% 0.17/0.36  #    Success case prop encoding time   : 0.000
% 0.17/0.36  #    Success case prop solver time     : 0.000
% 0.17/0.36  # Current number of processed clauses  : 24
% 0.17/0.36  #    Positive orientable unit clauses  : 7
% 0.17/0.36  #    Positive unorientable unit clauses: 0
% 0.17/0.36  #    Negative unit clauses             : 1
% 0.17/0.36  #    Non-unit-clauses                  : 16
% 0.17/0.36  # Current number of unprocessed clauses: 5
% 0.17/0.36  # ...number of literals in the above   : 22
% 0.17/0.36  # Current number of archived formulas  : 0
% 0.17/0.36  # Current number of archived clauses   : 24
% 0.17/0.36  # Clause-clause subsumption calls (NU) : 357
% 0.17/0.36  # Rec. Clause-clause subsumption calls : 51
% 0.17/0.36  # Non-unit clause-clause subsumptions  : 6
% 0.17/0.36  # Unit Clause-clause subsumption calls : 5
% 0.17/0.36  # Rewrite failures with RHS unbound    : 0
% 0.17/0.36  # BW rewrite match attempts            : 3
% 0.17/0.36  # BW rewrite match successes           : 1
% 0.17/0.36  # Condensation attempts                : 0
% 0.17/0.36  # Condensation successes               : 0
% 0.17/0.36  # Termbank termtop insertions          : 2094
% 0.17/0.36  
% 0.17/0.36  # -------------------------------------------------
% 0.17/0.36  # User time                : 0.032 s
% 0.17/0.36  # System time              : 0.005 s
% 0.17/0.36  # Total time               : 0.037 s
% 0.17/0.36  # Maximum resident set size: 1568 pages
%------------------------------------------------------------------------------
