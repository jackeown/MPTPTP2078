%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:13:22 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 ( 194 expanded)
%              Number of clauses        :   28 (  72 expanded)
%              Number of leaves         :    5 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  136 ( 973 expanded)
%              Number of equality atoms :    7 ( 108 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t36_tops_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v2_tops_2(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
                   => ( X4 = X2
                     => v2_tops_2(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tops_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(d2_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
         => ( v2_tops_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( r2_hidden(X3,X2)
                 => v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_2)).

fof(t34_tops_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( v4_pre_topc(X2,X1)
               => ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
                   => ( X4 = X2
                     => v4_pre_topc(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tops_2)).

fof(c_0_5,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
           => ! [X3] :
                ( m1_pre_topc(X3,X1)
               => ( v2_tops_2(X2,X1)
                 => ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))
                     => ( X4 = X2
                       => v2_tops_2(X4,X3) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t36_tops_2])).

fof(c_0_6,negated_conjecture,
    ( l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))
    & m1_pre_topc(esk4_0,esk2_0)
    & v2_tops_2(esk3_0,esk2_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    & esk5_0 = esk3_0
    & ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).

fof(c_0_7,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | l1_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_8,plain,(
    ! [X5,X6,X7] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(X7))
      | m1_subset_1(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_9,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_10,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_11,plain,(
    ! [X10,X11,X12] :
      ( ( ~ v2_tops_2(X11,X10)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ r2_hidden(X12,X11)
        | v4_pre_topc(X12,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk1_2(X10,X11),k1_zfmisc_1(u1_struct_0(X10)))
        | v2_tops_2(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(esk1_2(X10,X11),X11)
        | v2_tops_2(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ l1_pre_topc(X10) )
      & ( ~ v4_pre_topc(esk1_2(X10,X11),X10)
        | v2_tops_2(X11,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).

cnf(c_0_12,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_13,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_tops_2(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_16,plain,(
    ! [X14,X15,X16,X17] :
      ( ~ l1_pre_topc(X14)
      | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
      | ~ m1_pre_topc(X16,X14)
      | ~ v4_pre_topc(X15,X14)
      | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
      | X17 != X15
      | v4_pre_topc(X17,X16) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_tops_2])])])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_19,plain,
    ( r2_hidden(esk1_2(X1,X2),X2)
    | v2_tops_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_tops_2(esk3_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_15,c_0_10])).

cnf(c_0_22,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v2_tops_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_23,plain,
    ( v4_pre_topc(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X3,X1)
    | ~ v4_pre_topc(X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | X4 != X2 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(esk1_2(esk4_0,esk3_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_18]),c_0_20])]),c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_27,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v2_tops_2(X3,X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r2_hidden(X1,X3) ),
    inference(csr,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( v2_tops_2(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_29,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(X1,esk3_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v4_pre_topc(X1,esk2_0)
    | ~ r2_hidden(X1,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_26]),c_0_28]),c_0_14])])).

cnf(c_0_33,negated_conjecture,
    ( v4_pre_topc(esk1_2(esk4_0,esk3_0),esk4_0)
    | ~ v4_pre_topc(esk1_2(esk4_0,esk3_0),X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk1_2(esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk1_2(esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_31,c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v4_pre_topc(esk1_2(esk4_0,esk3_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_32,c_0_25])).

cnf(c_0_36,plain,
    ( v2_tops_2(X2,X1)
    | ~ v4_pre_topc(esk1_2(X1,X2),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_37,negated_conjecture,
    ( v4_pre_topc(esk1_2(esk4_0,esk3_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35]),c_0_13]),c_0_14])])).

cnf(c_0_38,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_37]),c_0_20]),c_0_18])]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.36  % Computer   : n006.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 09:36:22 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  # Version: 2.5pre002
% 0.14/0.36  # No SInE strategy applied
% 0.14/0.36  # Trying AutoSched0 for 299 seconds
% 0.21/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.21/0.39  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.21/0.39  #
% 0.21/0.39  # Preprocessing time       : 0.027 s
% 0.21/0.39  # Presaturation interreduction done
% 0.21/0.39  
% 0.21/0.39  # Proof found!
% 0.21/0.39  # SZS status Theorem
% 0.21/0.39  # SZS output start CNFRefutation
% 0.21/0.39  fof(t36_tops_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_pre_topc(X3,X1)=>(v2_tops_2(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))=>(X4=X2=>v2_tops_2(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_tops_2)).
% 0.21/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.39  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.21/0.39  fof(d2_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(v2_tops_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X3,X2)=>v4_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tops_2)).
% 0.21/0.39  fof(t34_tops_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_pre_topc(X3,X1)=>(v4_pre_topc(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))=>(X4=X2=>v4_pre_topc(X4,X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_tops_2)).
% 0.21/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m1_pre_topc(X3,X1)=>(v2_tops_2(X2,X1)=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X3))))=>(X4=X2=>v2_tops_2(X4,X3)))))))), inference(assume_negation,[status(cth)],[t36_tops_2])).
% 0.21/0.39  fof(c_0_6, negated_conjecture, (l1_pre_topc(esk2_0)&(m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))&(m1_pre_topc(esk4_0,esk2_0)&(v2_tops_2(esk3_0,esk2_0)&(m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))&(esk5_0=esk3_0&~v2_tops_2(esk5_0,esk4_0))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])).
% 0.21/0.39  fof(c_0_7, plain, ![X8, X9]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|l1_pre_topc(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.39  fof(c_0_8, plain, ![X5, X6, X7]:(~r2_hidden(X5,X6)|~m1_subset_1(X6,k1_zfmisc_1(X7))|m1_subset_1(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.21/0.39  cnf(c_0_9, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_10, negated_conjecture, (esk5_0=esk3_0), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  fof(c_0_11, plain, ![X10, X11, X12]:((~v2_tops_2(X11,X10)|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))|(~r2_hidden(X12,X11)|v4_pre_topc(X12,X10)))|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|~l1_pre_topc(X10))&((m1_subset_1(esk1_2(X10,X11),k1_zfmisc_1(u1_struct_0(X10)))|v2_tops_2(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|~l1_pre_topc(X10))&((r2_hidden(esk1_2(X10,X11),X11)|v2_tops_2(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|~l1_pre_topc(X10))&(~v4_pre_topc(esk1_2(X10,X11),X10)|v2_tops_2(X11,X10)|~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|~l1_pre_topc(X10))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_2])])])])])).
% 0.21/0.39  cnf(c_0_12, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.21/0.39  cnf(c_0_13, negated_conjecture, (m1_pre_topc(esk4_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_14, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_15, negated_conjecture, (~v2_tops_2(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  fof(c_0_16, plain, ![X14, X15, X16, X17]:(~l1_pre_topc(X14)|(~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|(~m1_pre_topc(X16,X14)|(~v4_pre_topc(X15,X14)|(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|(X17!=X15|v4_pre_topc(X17,X16))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_tops_2])])])).
% 0.21/0.39  cnf(c_0_17, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.21/0.39  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.21/0.39  cnf(c_0_19, plain, (r2_hidden(esk1_2(X1,X2),X2)|v2_tops_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])])).
% 0.21/0.39  cnf(c_0_21, negated_conjecture, (~v2_tops_2(esk3_0,esk4_0)), inference(rw,[status(thm)],[c_0_15, c_0_10])).
% 0.21/0.39  cnf(c_0_22, plain, (v4_pre_topc(X3,X2)|~v2_tops_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_23, plain, (v4_pre_topc(X4,X3)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X3,X1)|~v4_pre_topc(X2,X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|X4!=X2), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.39  cnf(c_0_24, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_18])).
% 0.21/0.39  cnf(c_0_25, negated_conjecture, (r2_hidden(esk1_2(esk4_0,esk3_0),esk3_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19, c_0_18]), c_0_20])]), c_0_21])).
% 0.21/0.39  cnf(c_0_26, negated_conjecture, (m1_subset_1(esk3_0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_27, plain, (v4_pre_topc(X1,X2)|~v2_tops_2(X3,X2)|~l1_pre_topc(X2)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r2_hidden(X1,X3)), inference(csr,[status(thm)],[c_0_22, c_0_17])).
% 0.21/0.39  cnf(c_0_28, negated_conjecture, (v2_tops_2(esk3_0,esk2_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.21/0.39  cnf(c_0_29, plain, (v4_pre_topc(X1,X2)|~v4_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_23])).
% 0.21/0.39  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk1_2(esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.21/0.39  cnf(c_0_31, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(X1,esk3_0)), inference(spm,[status(thm)],[c_0_17, c_0_26])).
% 0.21/0.39  cnf(c_0_32, negated_conjecture, (v4_pre_topc(X1,esk2_0)|~r2_hidden(X1,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_26]), c_0_28]), c_0_14])])).
% 0.21/0.39  cnf(c_0_33, negated_conjecture, (v4_pre_topc(esk1_2(esk4_0,esk3_0),esk4_0)|~v4_pre_topc(esk1_2(esk4_0,esk3_0),X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)|~m1_subset_1(esk1_2(esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.21/0.39  cnf(c_0_34, negated_conjecture, (m1_subset_1(esk1_2(esk4_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(spm,[status(thm)],[c_0_31, c_0_25])).
% 0.21/0.39  cnf(c_0_35, negated_conjecture, (v4_pre_topc(esk1_2(esk4_0,esk3_0),esk2_0)), inference(spm,[status(thm)],[c_0_32, c_0_25])).
% 0.21/0.39  cnf(c_0_36, plain, (v2_tops_2(X2,X1)|~v4_pre_topc(esk1_2(X1,X2),X1)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.21/0.39  cnf(c_0_37, negated_conjecture, (v4_pre_topc(esk1_2(esk4_0,esk3_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_35]), c_0_13]), c_0_14])])).
% 0.21/0.39  cnf(c_0_38, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_37]), c_0_20]), c_0_18])]), c_0_21]), ['proof']).
% 0.21/0.39  # SZS output end CNFRefutation
% 0.21/0.39  # Proof object total steps             : 39
% 0.21/0.39  # Proof object clause steps            : 28
% 0.21/0.39  # Proof object formula steps           : 11
% 0.21/0.39  # Proof object conjectures             : 23
% 0.21/0.39  # Proof object clause conjectures      : 20
% 0.21/0.39  # Proof object formula conjectures     : 3
% 0.21/0.39  # Proof object initial clauses used    : 13
% 0.21/0.39  # Proof object initial formulas used   : 5
% 0.21/0.39  # Proof object generating inferences   : 11
% 0.21/0.39  # Proof object simplifying inferences  : 20
% 0.21/0.39  # Training examples: 0 positive, 0 negative
% 0.21/0.39  # Parsed axioms                        : 5
% 0.21/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.39  # Initial clauses                      : 14
% 0.21/0.39  # Removed in clause preprocessing      : 0
% 0.21/0.39  # Initial clauses in saturation        : 14
% 0.21/0.39  # Processed clauses                    : 42
% 0.21/0.39  # ...of these trivial                  : 0
% 0.21/0.39  # ...subsumed                          : 1
% 0.21/0.39  # ...remaining for further processing  : 41
% 0.21/0.39  # Other redundant clauses eliminated   : 1
% 0.21/0.39  # Clauses deleted for lack of memory   : 0
% 0.21/0.39  # Backward-subsumed                    : 0
% 0.21/0.39  # Backward-rewritten                   : 1
% 0.21/0.39  # Generated clauses                    : 20
% 0.21/0.39  # ...of the previous two non-trivial   : 14
% 0.21/0.39  # Contextual simplify-reflections      : 1
% 0.21/0.39  # Paramodulations                      : 19
% 0.21/0.39  # Factorizations                       : 0
% 0.21/0.39  # Equation resolutions                 : 1
% 0.21/0.39  # Propositional unsat checks           : 0
% 0.21/0.39  #    Propositional check models        : 0
% 0.21/0.39  #    Propositional check unsatisfiable : 0
% 0.21/0.39  #    Propositional clauses             : 0
% 0.21/0.39  #    Propositional clauses after purity: 0
% 0.21/0.39  #    Propositional unsat core size     : 0
% 0.21/0.39  #    Propositional preprocessing time  : 0.000
% 0.21/0.39  #    Propositional encoding time       : 0.000
% 0.21/0.39  #    Propositional solver time         : 0.000
% 0.21/0.39  #    Success case prop preproc time    : 0.000
% 0.21/0.39  #    Success case prop encoding time   : 0.000
% 0.21/0.39  #    Success case prop solver time     : 0.000
% 0.21/0.39  # Current number of processed clauses  : 25
% 0.21/0.39  #    Positive orientable unit clauses  : 12
% 0.21/0.39  #    Positive unorientable unit clauses: 0
% 0.21/0.39  #    Negative unit clauses             : 1
% 0.21/0.39  #    Non-unit-clauses                  : 12
% 0.21/0.39  # Current number of unprocessed clauses: 0
% 0.21/0.39  # ...number of literals in the above   : 0
% 0.21/0.39  # Current number of archived formulas  : 0
% 0.21/0.39  # Current number of archived clauses   : 15
% 0.21/0.39  # Clause-clause subsumption calls (NU) : 33
% 0.21/0.39  # Rec. Clause-clause subsumption calls : 5
% 0.21/0.39  # Non-unit clause-clause subsumptions  : 1
% 0.21/0.39  # Unit Clause-clause subsumption calls : 0
% 0.21/0.39  # Rewrite failures with RHS unbound    : 0
% 0.21/0.39  # BW rewrite match attempts            : 4
% 0.21/0.39  # BW rewrite match successes           : 1
% 0.21/0.39  # Condensation attempts                : 0
% 0.21/0.39  # Condensation successes               : 0
% 0.21/0.39  # Termbank termtop insertions          : 1662
% 0.21/0.39  
% 0.21/0.39  # -------------------------------------------------
% 0.21/0.39  # User time                : 0.029 s
% 0.21/0.39  # System time              : 0.003 s
% 0.21/0.39  # Total time               : 0.032 s
% 0.21/0.39  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
