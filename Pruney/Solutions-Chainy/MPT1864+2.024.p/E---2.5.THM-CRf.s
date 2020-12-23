%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:42 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   35 (  81 expanded)
%              Number of clauses        :   22 (  29 expanded)
%              Number of leaves         :    6 (  20 expanded)
%              Depth                    :   10
%              Number of atoms          :  143 ( 500 expanded)
%              Number of equality atoms :   12 (  51 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   32 (   2 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t32_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k1_tarski(X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(d5_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ~ ( r1_tarski(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = X3 ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tex_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(t38_zfmisc_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_tarski(X1,X2),X3)
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v2_tex_2(X2,X1)
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ~ ( r2_hidden(X3,X2)
                      & ! [X4] :
                          ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v3_pre_topc(X4,X1)
                              & k9_subset_1(u1_struct_0(X1),X2,X4) = k1_tarski(X3) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t32_tex_2])).

fof(c_0_7,negated_conjecture,(
    ! [X23] :
      ( l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & v2_tex_2(esk4_0,esk3_0)
      & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
      & r2_hidden(esk5_0,esk4_0)
      & ( ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v3_pre_topc(X23,esk3_0)
        | k9_subset_1(u1_struct_0(esk3_0),esk4_0,X23) != k1_tarski(esk5_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).

fof(c_0_8,plain,(
    ! [X8] : k2_tarski(X8,X8) = k1_tarski(X8) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

cnf(c_0_9,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v3_pre_topc(X1,esk3_0)
    | k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X14,X15,X16,X19] :
      ( ( m1_subset_1(esk1_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r1_tarski(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ v2_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( v3_pre_topc(esk1_3(X14,X15,X16),X14)
        | ~ r1_tarski(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ v2_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( k9_subset_1(u1_struct_0(X14),X15,esk1_3(X14,X15,X16)) = X16
        | ~ r1_tarski(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ v2_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))
        | v2_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( r1_tarski(esk2_2(X14,X15),X15)
        | v2_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) )
      & ( ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ v3_pre_topc(X19,X14)
        | k9_subset_1(u1_struct_0(X14),X15,X19) != esk2_2(X14,X15)
        | v2_tex_2(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

cnf(c_0_12,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1) != k2_tarski(esk5_0,esk5_0)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(rw,[status(thm)],[c_0_9,c_0_10])).

cnf(c_0_13,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_17,negated_conjecture,
    ( ~ v3_pre_topc(esk1_3(esk3_0,esk4_0,k2_tarski(esk5_0,esk5_0)),esk3_0)
    | ~ m1_subset_1(esk1_3(esk3_0,esk4_0,k2_tarski(esk5_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16])])])).

cnf(c_0_18,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X12,X13] :
      ( ( ~ m1_subset_1(X12,k1_zfmisc_1(X13))
        | r1_tarski(X12,X13) )
      & ( ~ r1_tarski(X12,X13)
        | m1_subset_1(X12,k1_zfmisc_1(X13)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_20,negated_conjecture,
    ( ~ v3_pre_topc(esk1_3(esk3_0,esk4_0,k2_tarski(esk5_0,esk5_0)),esk3_0)
    | ~ m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_21,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_22,plain,(
    ! [X5,X6,X7] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X6,X7)
      | r1_tarski(X5,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,negated_conjecture,
    ( ~ m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_14]),c_0_15]),c_0_16])])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_27,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(esk5_0,esk5_0),u1_struct_0(esk3_0))
    | ~ r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk3_0))
    | ~ r1_tarski(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

fof(c_0_30,plain,(
    ! [X9,X10,X11] :
      ( ( r2_hidden(X9,X11)
        | ~ r1_tarski(k2_tarski(X9,X10),X11) )
      & ( r2_hidden(X10,X11)
        | ~ r1_tarski(k2_tarski(X9,X10),X11) )
      & ( ~ r2_hidden(X9,X11)
        | ~ r2_hidden(X10,X11)
        | r1_tarski(k2_tarski(X9,X10),X11) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_32,plain,
    ( r1_tarski(k2_tarski(X1,X3),X2)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_34,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.32  % Computer   : n021.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 15:42:49 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  # Version: 2.5pre002
% 0.13/0.33  # No SInE strategy applied
% 0.13/0.33  # Trying AutoSched0 for 299 seconds
% 0.13/0.34  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.13/0.34  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.13/0.34  #
% 0.13/0.34  # Preprocessing time       : 0.014 s
% 0.13/0.34  
% 0.13/0.34  # Proof found!
% 0.13/0.34  # SZS status Theorem
% 0.13/0.34  # SZS output start CNFRefutation
% 0.13/0.34  fof(t32_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 0.13/0.34  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.13/0.34  fof(d5_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 0.13/0.34  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.13/0.34  fof(t1_xboole_1, axiom, ![X1, X2, X3]:((r1_tarski(X1,X2)&r1_tarski(X2,X3))=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 0.13/0.34  fof(t38_zfmisc_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_tarski(X1,X2),X3)<=>(r2_hidden(X1,X3)&r2_hidden(X2,X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 0.13/0.34  fof(c_0_6, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3))))))))))), inference(assume_negation,[status(cth)],[t32_tex_2])).
% 0.13/0.34  fof(c_0_7, negated_conjecture, ![X23]:(l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(v2_tex_2(esk4_0,esk3_0)&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(r2_hidden(esk5_0,esk4_0)&(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(esk3_0)))|(~v3_pre_topc(X23,esk3_0)|k9_subset_1(u1_struct_0(esk3_0),esk4_0,X23)!=k1_tarski(esk5_0)))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])])).
% 0.13/0.34  fof(c_0_8, plain, ![X8]:k2_tarski(X8,X8)=k1_tarski(X8), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.13/0.34  cnf(c_0_9, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v3_pre_topc(X1,esk3_0)|k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.34  cnf(c_0_10, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.13/0.34  fof(c_0_11, plain, ![X14, X15, X16, X19]:(((m1_subset_1(esk1_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14)))|~r1_tarski(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~v2_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&((v3_pre_topc(esk1_3(X14,X15,X16),X14)|~r1_tarski(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~v2_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(k9_subset_1(u1_struct_0(X14),X15,esk1_3(X14,X15,X16))=X16|~r1_tarski(X16,X15)|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X14)))|~v2_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))))&((m1_subset_1(esk2_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))|v2_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&((r1_tarski(esk2_2(X14,X15),X15)|v2_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))&(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X14)))|(~v3_pre_topc(X19,X14)|k9_subset_1(u1_struct_0(X14),X15,X19)!=esk2_2(X14,X15))|v2_tex_2(X15,X14)|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~l1_pre_topc(X14))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).
% 0.13/0.34  cnf(c_0_12, negated_conjecture, (k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1)!=k2_tarski(esk5_0,esk5_0)|~v3_pre_topc(X1,esk3_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(rw,[status(thm)],[c_0_9, c_0_10])).
% 0.13/0.34  cnf(c_0_13, plain, (k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3))=X3|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.34  cnf(c_0_14, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.34  cnf(c_0_15, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.34  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.34  cnf(c_0_17, negated_conjecture, (~v3_pre_topc(esk1_3(esk3_0,esk4_0,k2_tarski(esk5_0,esk5_0)),esk3_0)|~m1_subset_1(esk1_3(esk3_0,esk4_0,k2_tarski(esk5_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16])])])).
% 0.13/0.34  cnf(c_0_18, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.34  fof(c_0_19, plain, ![X12, X13]:((~m1_subset_1(X12,k1_zfmisc_1(X13))|r1_tarski(X12,X13))&(~r1_tarski(X12,X13)|m1_subset_1(X12,k1_zfmisc_1(X13)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.13/0.34  cnf(c_0_20, negated_conjecture, (~v3_pre_topc(esk1_3(esk3_0,esk4_0,k2_tarski(esk5_0,esk5_0)),esk3_0)|~m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.34  cnf(c_0_21, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.13/0.34  fof(c_0_22, plain, ![X5, X6, X7]:(~r1_tarski(X5,X6)|~r1_tarski(X6,X7)|r1_tarski(X5,X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).
% 0.13/0.34  cnf(c_0_23, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.34  cnf(c_0_24, negated_conjecture, (~m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_14]), c_0_15]), c_0_16])])).
% 0.13/0.34  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.13/0.34  cnf(c_0_26, plain, (r1_tarski(X1,X3)|~r1_tarski(X1,X2)|~r1_tarski(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.13/0.34  cnf(c_0_27, negated_conjecture, (r1_tarski(esk4_0,u1_struct_0(esk3_0))), inference(spm,[status(thm)],[c_0_23, c_0_16])).
% 0.13/0.34  cnf(c_0_28, negated_conjecture, (~r1_tarski(k2_tarski(esk5_0,esk5_0),u1_struct_0(esk3_0))|~r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.13/0.34  cnf(c_0_29, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk3_0))|~r1_tarski(X1,esk4_0)), inference(spm,[status(thm)],[c_0_26, c_0_27])).
% 0.13/0.34  fof(c_0_30, plain, ![X9, X10, X11]:(((r2_hidden(X9,X11)|~r1_tarski(k2_tarski(X9,X10),X11))&(r2_hidden(X10,X11)|~r1_tarski(k2_tarski(X9,X10),X11)))&(~r2_hidden(X9,X11)|~r2_hidden(X10,X11)|r1_tarski(k2_tarski(X9,X10),X11))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_zfmisc_1])])])).
% 0.13/0.34  cnf(c_0_31, negated_conjecture, (~r1_tarski(k2_tarski(esk5_0,esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.13/0.34  cnf(c_0_32, plain, (r1_tarski(k2_tarski(X1,X3),X2)|~r2_hidden(X1,X2)|~r2_hidden(X3,X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.13/0.34  cnf(c_0_33, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.13/0.34  cnf(c_0_34, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])]), ['proof']).
% 0.13/0.34  # SZS output end CNFRefutation
% 0.13/0.34  # Proof object total steps             : 35
% 0.13/0.34  # Proof object clause steps            : 22
% 0.13/0.34  # Proof object formula steps           : 13
% 0.13/0.34  # Proof object conjectures             : 17
% 0.13/0.34  # Proof object clause conjectures      : 14
% 0.13/0.34  # Proof object formula conjectures     : 3
% 0.13/0.34  # Proof object initial clauses used    : 13
% 0.13/0.34  # Proof object initial formulas used   : 6
% 0.13/0.34  # Proof object generating inferences   : 8
% 0.13/0.34  # Proof object simplifying inferences  : 16
% 0.13/0.34  # Training examples: 0 positive, 0 negative
% 0.13/0.34  # Parsed axioms                        : 6
% 0.13/0.34  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.34  # Initial clauses                      : 19
% 0.13/0.34  # Removed in clause preprocessing      : 1
% 0.13/0.34  # Initial clauses in saturation        : 18
% 0.13/0.34  # Processed clauses                    : 27
% 0.13/0.34  # ...of these trivial                  : 0
% 0.13/0.34  # ...subsumed                          : 0
% 0.13/0.34  # ...remaining for further processing  : 27
% 0.13/0.34  # Other redundant clauses eliminated   : 1
% 0.13/0.34  # Clauses deleted for lack of memory   : 0
% 0.13/0.34  # Backward-subsumed                    : 2
% 0.13/0.34  # Backward-rewritten                   : 0
% 0.13/0.34  # Generated clauses                    : 23
% 0.13/0.34  # ...of the previous two non-trivial   : 17
% 0.13/0.34  # Contextual simplify-reflections      : 0
% 0.13/0.34  # Paramodulations                      : 22
% 0.13/0.34  # Factorizations                       : 0
% 0.13/0.34  # Equation resolutions                 : 1
% 0.13/0.34  # Propositional unsat checks           : 0
% 0.13/0.34  #    Propositional check models        : 0
% 0.13/0.34  #    Propositional check unsatisfiable : 0
% 0.13/0.34  #    Propositional clauses             : 0
% 0.13/0.34  #    Propositional clauses after purity: 0
% 0.13/0.34  #    Propositional unsat core size     : 0
% 0.13/0.34  #    Propositional preprocessing time  : 0.000
% 0.13/0.34  #    Propositional encoding time       : 0.000
% 0.13/0.34  #    Propositional solver time         : 0.000
% 0.13/0.34  #    Success case prop preproc time    : 0.000
% 0.13/0.34  #    Success case prop encoding time   : 0.000
% 0.13/0.34  #    Success case prop solver time     : 0.000
% 0.13/0.34  # Current number of processed clauses  : 25
% 0.13/0.34  #    Positive orientable unit clauses  : 6
% 0.13/0.34  #    Positive unorientable unit clauses: 0
% 0.13/0.34  #    Negative unit clauses             : 2
% 0.13/0.34  #    Non-unit-clauses                  : 17
% 0.13/0.34  # Current number of unprocessed clauses: 8
% 0.13/0.34  # ...number of literals in the above   : 30
% 0.13/0.34  # Current number of archived formulas  : 0
% 0.13/0.34  # Current number of archived clauses   : 3
% 0.13/0.34  # Clause-clause subsumption calls (NU) : 84
% 0.13/0.34  # Rec. Clause-clause subsumption calls : 40
% 0.13/0.34  # Non-unit clause-clause subsumptions  : 2
% 0.13/0.34  # Unit Clause-clause subsumption calls : 4
% 0.13/0.34  # Rewrite failures with RHS unbound    : 0
% 0.13/0.34  # BW rewrite match attempts            : 0
% 0.13/0.34  # BW rewrite match successes           : 0
% 0.13/0.34  # Condensation attempts                : 0
% 0.13/0.34  # Condensation successes               : 0
% 0.13/0.34  # Termbank termtop insertions          : 1882
% 0.13/0.34  
% 0.13/0.34  # -------------------------------------------------
% 0.13/0.34  # User time                : 0.014 s
% 0.13/0.34  # System time              : 0.003 s
% 0.13/0.34  # Total time               : 0.017 s
% 0.13/0.34  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
