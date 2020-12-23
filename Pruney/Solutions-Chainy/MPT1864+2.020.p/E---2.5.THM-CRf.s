%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:41 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   29 (  77 expanded)
%              Number of clauses        :   18 (  26 expanded)
%              Number of leaves         :    5 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  127 ( 503 expanded)
%              Number of equality atoms :    8 (  50 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   32 (   3 average)
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

fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(t37_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(k1_tarski(X1),X2)
    <=> r2_hidden(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(c_0_5,negated_conjecture,(
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

fof(c_0_6,negated_conjecture,(
    ! [X21] :
      ( l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & v2_tex_2(esk4_0,esk3_0)
      & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
      & r2_hidden(esk5_0,esk4_0)
      & ( ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ v3_pre_topc(X21,esk3_0)
        | k9_subset_1(u1_struct_0(esk3_0),esk4_0,X21) != k1_tarski(esk5_0) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).

fof(c_0_7,plain,(
    ! [X12,X13,X14,X17] :
      ( ( m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))
        | ~ r1_tarski(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( v3_pre_topc(esk1_3(X12,X13,X14),X12)
        | ~ r1_tarski(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( k9_subset_1(u1_struct_0(X12),X13,esk1_3(X12,X13,X14)) = X14
        | ~ r1_tarski(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( m1_subset_1(esk2_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( r1_tarski(esk2_2(X12,X13),X13)
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) )
      & ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ v3_pre_topc(X17,X12)
        | k9_subset_1(u1_struct_0(X12),X13,X17) != esk2_2(X12,X13)
        | v2_tex_2(X13,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))
        | ~ l1_pre_topc(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).

cnf(c_0_8,negated_conjecture,
    ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ v3_pre_topc(X1,esk3_0)
    | k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1) != k1_tarski(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_9,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3)) = X3
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( v2_tex_2(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_12,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_13,negated_conjecture,
    ( ~ v3_pre_topc(esk1_3(esk3_0,esk4_0,k1_tarski(esk5_0)),esk3_0)
    | ~ m1_subset_1(esk1_3(esk3_0,esk4_0,k1_tarski(esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tarski(esk5_0),esk4_0) ),
    inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8,c_0_9]),c_0_10]),c_0_11]),c_0_12])])])).

cnf(c_0_14,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_15,negated_conjecture,
    ( ~ v3_pre_topc(esk1_3(esk3_0,esk4_0,k1_tarski(esk5_0)),esk3_0)
    | ~ m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tarski(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13,c_0_14]),c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_16,plain,
    ( v3_pre_topc(esk1_3(X1,X2,X3),X1)
    | ~ r1_tarski(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

fof(c_0_17,plain,(
    ! [X10,X11] :
      ( ~ r2_hidden(X10,X11)
      | m1_subset_1(k1_tarski(X10),k1_zfmisc_1(X11)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

cnf(c_0_18,negated_conjecture,
    ( ~ m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(k1_tarski(esk5_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_10]),c_0_11]),c_0_12])])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_20,plain,(
    ! [X5,X6] :
      ( ( ~ r1_tarski(k1_tarski(X5),X6)
        | r2_hidden(X5,X6) )
      & ( ~ r2_hidden(X5,X6)
        | r1_tarski(k1_tarski(X5),X6) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).

fof(c_0_21,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(X7))
      | ~ r2_hidden(X9,X8)
      | r2_hidden(X9,X7) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

cnf(c_0_22,negated_conjecture,
    ( ~ r2_hidden(esk5_0,u1_struct_0(esk3_0))
    | ~ r1_tarski(k1_tarski(esk5_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_23,plain,
    ( r1_tarski(k1_tarski(X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_25,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_26,negated_conjecture,
    ( ~ r2_hidden(esk5_0,u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_27,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk3_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_12])).

cnf(c_0_28,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:24:32 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.39  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.14/0.39  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.14/0.39  #
% 0.14/0.39  # Preprocessing time       : 0.049 s
% 0.14/0.39  
% 0.14/0.39  # Proof found!
% 0.14/0.39  # SZS status Theorem
% 0.14/0.39  # SZS output start CNFRefutation
% 0.14/0.39  fof(t32_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_tex_2)).
% 0.14/0.39  fof(d5_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>~((r1_tarski(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tex_2)).
% 0.14/0.39  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.14/0.39  fof(t37_zfmisc_1, axiom, ![X1, X2]:(r1_tarski(k1_tarski(X1),X2)<=>r2_hidden(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_zfmisc_1)).
% 0.14/0.39  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.14/0.39  fof(c_0_5, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v2_tex_2(X2,X1)=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>~((r2_hidden(X3,X2)&![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))=>~((v3_pre_topc(X4,X1)&k9_subset_1(u1_struct_0(X1),X2,X4)=k1_tarski(X3))))))))))), inference(assume_negation,[status(cth)],[t32_tex_2])).
% 0.14/0.39  fof(c_0_6, negated_conjecture, ![X21]:(l1_pre_topc(esk3_0)&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(v2_tex_2(esk4_0,esk3_0)&(m1_subset_1(esk5_0,u1_struct_0(esk3_0))&(r2_hidden(esk5_0,esk4_0)&(~m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(esk3_0)))|(~v3_pre_topc(X21,esk3_0)|k9_subset_1(u1_struct_0(esk3_0),esk4_0,X21)!=k1_tarski(esk5_0)))))))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_5])])])])).
% 0.14/0.39  fof(c_0_7, plain, ![X12, X13, X14, X17]:(((m1_subset_1(esk1_3(X12,X13,X14),k1_zfmisc_1(u1_struct_0(X12)))|~r1_tarski(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&((v3_pre_topc(esk1_3(X12,X13,X14),X12)|~r1_tarski(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(k9_subset_1(u1_struct_0(X12),X13,esk1_3(X12,X13,X14))=X14|~r1_tarski(X14,X13)|~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X12)))|~v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))))&((m1_subset_1(esk2_2(X12,X13),k1_zfmisc_1(u1_struct_0(X12)))|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&((r1_tarski(esk2_2(X12,X13),X13)|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))&(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X12)))|(~v3_pre_topc(X17,X12)|k9_subset_1(u1_struct_0(X12),X13,X17)!=esk2_2(X12,X13))|v2_tex_2(X13,X12)|~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X12)))|~l1_pre_topc(X12))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_tex_2])])])])])).
% 0.14/0.39  cnf(c_0_8, negated_conjecture, (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~v3_pre_topc(X1,esk3_0)|k9_subset_1(u1_struct_0(esk3_0),esk4_0,X1)!=k1_tarski(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.39  cnf(c_0_9, plain, (k9_subset_1(u1_struct_0(X1),X2,esk1_3(X1,X2,X3))=X3|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.40  cnf(c_0_10, negated_conjecture, (v2_tex_2(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.40  cnf(c_0_11, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.40  cnf(c_0_12, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.40  cnf(c_0_13, negated_conjecture, (~v3_pre_topc(esk1_3(esk3_0,esk4_0,k1_tarski(esk5_0)),esk3_0)|~m1_subset_1(esk1_3(esk3_0,esk4_0,k1_tarski(esk5_0)),k1_zfmisc_1(u1_struct_0(esk3_0)))|~m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tarski(esk5_0),esk4_0)), inference(er,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_8, c_0_9]), c_0_10]), c_0_11]), c_0_12])])])).
% 0.14/0.40  cnf(c_0_14, plain, (m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.40  cnf(c_0_15, negated_conjecture, (~v3_pre_topc(esk1_3(esk3_0,esk4_0,k1_tarski(esk5_0)),esk3_0)|~m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tarski(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_13, c_0_14]), c_0_10]), c_0_11]), c_0_12])])).
% 0.14/0.40  cnf(c_0_16, plain, (v3_pre_topc(esk1_3(X1,X2,X3),X1)|~r1_tarski(X3,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_tex_2(X2,X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.14/0.40  fof(c_0_17, plain, ![X10, X11]:(~r2_hidden(X10,X11)|m1_subset_1(k1_tarski(X10),k1_zfmisc_1(X11))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.14/0.40  cnf(c_0_18, negated_conjecture, (~m1_subset_1(k1_tarski(esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(k1_tarski(esk5_0),esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_10]), c_0_11]), c_0_12])])).
% 0.14/0.40  cnf(c_0_19, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.14/0.40  fof(c_0_20, plain, ![X5, X6]:((~r1_tarski(k1_tarski(X5),X6)|r2_hidden(X5,X6))&(~r2_hidden(X5,X6)|r1_tarski(k1_tarski(X5),X6))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t37_zfmisc_1])])).
% 0.14/0.40  fof(c_0_21, plain, ![X7, X8, X9]:(~m1_subset_1(X8,k1_zfmisc_1(X7))|(~r2_hidden(X9,X8)|r2_hidden(X9,X7))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.14/0.40  cnf(c_0_22, negated_conjecture, (~r2_hidden(esk5_0,u1_struct_0(esk3_0))|~r1_tarski(k1_tarski(esk5_0),esk4_0)), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.14/0.40  cnf(c_0_23, plain, (r1_tarski(k1_tarski(X1),X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.14/0.40  cnf(c_0_24, negated_conjecture, (r2_hidden(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.14/0.40  cnf(c_0_25, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.40  cnf(c_0_26, negated_conjecture, (~r2_hidden(esk5_0,u1_struct_0(esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.14/0.40  cnf(c_0_27, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk3_0))|~r2_hidden(X1,esk4_0)), inference(spm,[status(thm)],[c_0_25, c_0_12])).
% 0.14/0.40  cnf(c_0_28, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_24])]), ['proof']).
% 0.14/0.40  # SZS output end CNFRefutation
% 0.14/0.40  # Proof object total steps             : 29
% 0.14/0.40  # Proof object clause steps            : 18
% 0.14/0.40  # Proof object formula steps           : 11
% 0.14/0.40  # Proof object conjectures             : 15
% 0.14/0.40  # Proof object clause conjectures      : 12
% 0.14/0.40  # Proof object formula conjectures     : 3
% 0.14/0.40  # Proof object initial clauses used    : 11
% 0.14/0.40  # Proof object initial formulas used   : 5
% 0.14/0.40  # Proof object generating inferences   : 7
% 0.14/0.40  # Proof object simplifying inferences  : 17
% 0.14/0.40  # Training examples: 0 positive, 0 negative
% 0.14/0.40  # Parsed axioms                        : 5
% 0.14/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.40  # Initial clauses                      : 16
% 0.14/0.40  # Removed in clause preprocessing      : 0
% 0.14/0.40  # Initial clauses in saturation        : 16
% 0.14/0.40  # Processed clauses                    : 23
% 0.14/0.40  # ...of these trivial                  : 0
% 0.14/0.40  # ...subsumed                          : 0
% 0.14/0.40  # ...remaining for further processing  : 23
% 0.14/0.40  # Other redundant clauses eliminated   : 1
% 0.14/0.40  # Clauses deleted for lack of memory   : 0
% 0.14/0.40  # Backward-subsumed                    : 2
% 0.14/0.40  # Backward-rewritten                   : 0
% 0.14/0.40  # Generated clauses                    : 13
% 0.14/0.40  # ...of the previous two non-trivial   : 9
% 0.14/0.40  # Contextual simplify-reflections      : 0
% 0.14/0.40  # Paramodulations                      : 12
% 0.14/0.40  # Factorizations                       : 0
% 0.14/0.40  # Equation resolutions                 : 1
% 0.14/0.40  # Propositional unsat checks           : 0
% 0.14/0.40  #    Propositional check models        : 0
% 0.14/0.40  #    Propositional check unsatisfiable : 0
% 0.14/0.40  #    Propositional clauses             : 0
% 0.14/0.40  #    Propositional clauses after purity: 0
% 0.14/0.40  #    Propositional unsat core size     : 0
% 0.14/0.40  #    Propositional preprocessing time  : 0.000
% 0.14/0.40  #    Propositional encoding time       : 0.000
% 0.14/0.40  #    Propositional solver time         : 0.000
% 0.14/0.40  #    Success case prop preproc time    : 0.000
% 0.14/0.40  #    Success case prop encoding time   : 0.000
% 0.14/0.40  #    Success case prop solver time     : 0.000
% 0.14/0.40  # Current number of processed clauses  : 21
% 0.14/0.40  #    Positive orientable unit clauses  : 5
% 0.14/0.40  #    Positive unorientable unit clauses: 0
% 0.14/0.40  #    Negative unit clauses             : 1
% 0.14/0.40  #    Non-unit-clauses                  : 15
% 0.14/0.40  # Current number of unprocessed clauses: 2
% 0.14/0.40  # ...number of literals in the above   : 12
% 0.14/0.40  # Current number of archived formulas  : 0
% 0.14/0.40  # Current number of archived clauses   : 2
% 0.14/0.40  # Clause-clause subsumption calls (NU) : 68
% 0.14/0.40  # Rec. Clause-clause subsumption calls : 21
% 0.14/0.40  # Non-unit clause-clause subsumptions  : 2
% 0.14/0.40  # Unit Clause-clause subsumption calls : 3
% 0.14/0.40  # Rewrite failures with RHS unbound    : 0
% 0.14/0.40  # BW rewrite match attempts            : 0
% 0.14/0.40  # BW rewrite match successes           : 0
% 0.14/0.40  # Condensation attempts                : 0
% 0.14/0.40  # Condensation successes               : 0
% 0.14/0.40  # Termbank termtop insertions          : 1671
% 0.14/0.40  
% 0.14/0.40  # -------------------------------------------------
% 0.14/0.40  # User time                : 0.047 s
% 0.14/0.40  # System time              : 0.008 s
% 0.14/0.40  # Total time               : 0.055 s
% 0.14/0.40  # Maximum resident set size: 1572 pages
%------------------------------------------------------------------------------
