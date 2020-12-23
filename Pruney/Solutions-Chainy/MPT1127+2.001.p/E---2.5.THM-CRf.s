%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:20 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 (11529 expanded)
%              Number of clauses        :   73 (5102 expanded)
%              Number of leaves         :    6 (2917 expanded)
%              Depth                    :   24
%              Number of atoms          :  355 (39523 expanded)
%              Number of equality atoms :   46 (7310 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(t58_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_pre_topc)).

fof(d1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(X1)
      <=> ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
             => ( r1_tarski(X2,u1_pre_topc(X1))
               => r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) ) )
          & ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X1))
                      & r2_hidden(X3,u1_pre_topc(X1)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(c_0_6,plain,(
    ! [X16,X17,X18,X19] :
      ( ( X16 = X18
        | g1_pre_topc(X16,X17) != g1_pre_topc(X18,X19)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) )
      & ( X17 = X19
        | g1_pre_topc(X16,X17) != g1_pre_topc(X18,X19)
        | ~ m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_7,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | m1_subset_1(u1_pre_topc(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_8,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

fof(c_0_9,plain,(
    ! [X13,X14] :
      ( ( v1_pre_topc(g1_pre_topc(X13,X14))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) )
      & ( l1_pre_topc(g1_pre_topc(X13,X14))
        | ~ m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_10,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_11,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_12,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_13,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_14,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_15,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_10,c_0_11])).

cnf(c_0_16,plain,
    ( g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),u1_pre_topc(g1_pre_topc(X1,X2))) = g1_pre_topc(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14])).

fof(c_0_17,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => v2_pre_topc(X1) ) ) ),
    inference(assume_negation,[status(cth)],[t58_pre_topc])).

cnf(c_0_18,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( u1_struct_0(X1) = u1_struct_0(g1_pre_topc(X2,X3))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    & ~ v2_pre_topc(esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_21,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_22,plain,
    ( u1_struct_0(X1) = u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( u1_pre_topc(X1) = u1_pre_topc(g1_pre_topc(X2,X3))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_26,plain,
    ( u1_pre_topc(X1) = u1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_24,c_0_11])).

cnf(c_0_27,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = u1_struct_0(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) != g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_25])).

cnf(c_0_28,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_pre_topc(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_30,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != g1_pre_topc(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_16]),c_0_14])).

cnf(c_0_31,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_11])).

fof(c_0_32,plain,(
    ! [X6,X7,X8,X9] :
      ( ( r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ r1_tarski(X7,u1_pre_topc(X6))
        | r2_hidden(k5_setfam_1(u1_struct_0(X6),X7),u1_pre_topc(X6))
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(X8,u1_pre_topc(X6))
        | ~ r2_hidden(X9,u1_pre_topc(X6))
        | r2_hidden(k9_subset_1(u1_struct_0(X6),X8,X9),u1_pre_topc(X6))
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk2_1(X6),k1_zfmisc_1(u1_struct_0(X6)))
        | m1_subset_1(esk1_1(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk3_1(X6),k1_zfmisc_1(u1_struct_0(X6)))
        | m1_subset_1(esk1_1(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_1(X6),u1_pre_topc(X6))
        | m1_subset_1(esk1_1(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk3_1(X6),u1_pre_topc(X6))
        | m1_subset_1(esk1_1(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X6),esk2_1(X6),esk3_1(X6)),u1_pre_topc(X6))
        | m1_subset_1(esk1_1(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk2_1(X6),k1_zfmisc_1(u1_struct_0(X6)))
        | r1_tarski(esk1_1(X6),u1_pre_topc(X6))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk3_1(X6),k1_zfmisc_1(u1_struct_0(X6)))
        | r1_tarski(esk1_1(X6),u1_pre_topc(X6))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_1(X6),u1_pre_topc(X6))
        | r1_tarski(esk1_1(X6),u1_pre_topc(X6))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk3_1(X6),u1_pre_topc(X6))
        | r1_tarski(esk1_1(X6),u1_pre_topc(X6))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X6),esk2_1(X6),esk3_1(X6)),u1_pre_topc(X6))
        | r1_tarski(esk1_1(X6),u1_pre_topc(X6))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk2_1(X6),k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X6),esk1_1(X6)),u1_pre_topc(X6))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk3_1(X6),k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X6),esk1_1(X6)),u1_pre_topc(X6))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_1(X6),u1_pre_topc(X6))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X6),esk1_1(X6)),u1_pre_topc(X6))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk3_1(X6),u1_pre_topc(X6))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X6),esk1_1(X6)),u1_pre_topc(X6))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X6),esk2_1(X6),esk3_1(X6)),u1_pre_topc(X6))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X6),esk1_1(X6)),u1_pre_topc(X6))
        | ~ r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))
        | v2_pre_topc(X6)
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

cnf(c_0_33,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_31]),c_0_23])])).

cnf(c_0_34,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_35,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_36,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))) = u1_pre_topc(esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))) != g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_35])])).

cnf(c_0_38,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_pre_topc(esk4_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_28]),c_0_23])])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_28]),c_0_23])])).

cnf(c_0_40,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_pre_topc(esk4_0)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_14])).

cnf(c_0_41,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_14])).

cnf(c_0_42,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_43,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) = u1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_11]),c_0_23])])).

cnf(c_0_44,plain,
    ( r2_hidden(esk3_1(X1),u1_pre_topc(X1))
    | m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_11]),c_0_23])])).

cnf(c_0_46,negated_conjecture,
    ( ~ v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,plain,
    ( r2_hidden(esk3_1(X1),u1_pre_topc(X1))
    | r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_48,plain,
    ( r2_hidden(esk2_1(X1),u1_pre_topc(X1))
    | m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_49,plain,
    ( r2_hidden(esk2_1(X1),u1_pre_topc(X1))
    | r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_50,plain,
    ( r2_hidden(esk3_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(k5_setfam_1(u1_struct_0(esk4_0),X1),u1_pre_topc(esk4_0))
    | ~ r1_tarski(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_33]),c_0_35])]),c_0_43]),c_0_43])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | r2_hidden(esk3_1(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_23])]),c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(esk1_1(esk4_0),u1_pre_topc(esk4_0))
    | r2_hidden(esk3_1(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_45]),c_0_23])]),c_0_46])).

cnf(c_0_54,plain,
    ( r2_hidden(esk2_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_45]),c_0_23])]),c_0_46])).

cnf(c_0_56,negated_conjecture,
    ( r1_tarski(esk1_1(esk4_0),u1_pre_topc(esk4_0))
    | r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_45]),c_0_23])]),c_0_46])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),u1_pre_topc(esk4_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_45]),c_0_23])]),c_0_46]),c_0_52]),c_0_53])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_51]),c_0_45]),c_0_23])]),c_0_46]),c_0_55]),c_0_56])).

cnf(c_0_59,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_60,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_61,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_62,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_63,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X2),X1,X3),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),u1_pre_topc(esk4_0))
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_57,c_0_14])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0))
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_14])).

cnf(c_0_66,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | m1_subset_1(esk2_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_45]),c_0_23])]),c_0_46])).

cnf(c_0_68,negated_conjecture,
    ( r1_tarski(esk1_1(esk4_0),u1_pre_topc(esk4_0))
    | m1_subset_1(esk2_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_45]),c_0_23])]),c_0_46])).

cnf(c_0_69,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | m1_subset_1(esk3_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_45]),c_0_23])]),c_0_46])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk1_1(esk4_0),u1_pre_topc(esk4_0))
    | m1_subset_1(esk3_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_45]),c_0_23])]),c_0_46])).

cnf(c_0_72,plain,
    ( v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk4_0),X1,X2),u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X2,u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_33]),c_0_35])]),c_0_43]),c_0_43]),c_0_43])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(esk3_1(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_11]),c_0_23])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_11]),c_0_23])])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk2_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_51]),c_0_45]),c_0_23])]),c_0_46]),c_0_67]),c_0_68])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk3_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_51]),c_0_45]),c_0_23])]),c_0_46]),c_0_70]),c_0_71])).

cnf(c_0_78,plain,
    ( r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(esk4_0),esk1_1(esk4_0)),u1_pre_topc(esk4_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_45]),c_0_23]),c_0_74]),c_0_75])]),c_0_46]),c_0_76]),c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( r1_tarski(esk1_1(esk4_0),u1_pre_topc(esk4_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_73]),c_0_45]),c_0_23]),c_0_74]),c_0_75])]),c_0_46]),c_0_68]),c_0_71])).

cnf(c_0_81,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_82,negated_conjecture,
    ( ~ m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_51]),c_0_80])).

cnf(c_0_83,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_73]),c_0_45]),c_0_23]),c_0_74]),c_0_75])]),c_0_46]),c_0_67]),c_0_70]),c_0_82])).

cnf(c_0_84,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_83,c_0_14])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_11]),c_0_23])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:55:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.46  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.20/0.46  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.20/0.46  #
% 0.20/0.46  # Preprocessing time       : 0.027 s
% 0.20/0.46  # Presaturation interreduction done
% 0.20/0.46  
% 0.20/0.46  # Proof found!
% 0.20/0.46  # SZS status Theorem
% 0.20/0.46  # SZS output start CNFRefutation
% 0.20/0.46  fof(free_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>![X3, X4]:(g1_pre_topc(X1,X2)=g1_pre_topc(X3,X4)=>(X1=X3&X2=X4))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 0.20/0.46  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.20/0.46  fof(abstractness_v1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_pre_topc(X1)=>X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 0.20/0.46  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.20/0.46  fof(t58_pre_topc, conjecture, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>v2_pre_topc(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_pre_topc)).
% 0.20/0.46  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.20/0.46  fof(c_0_6, plain, ![X16, X17, X18, X19]:((X16=X18|g1_pre_topc(X16,X17)!=g1_pre_topc(X18,X19)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))))&(X17=X19|g1_pre_topc(X16,X17)!=g1_pre_topc(X18,X19)|~m1_subset_1(X17,k1_zfmisc_1(k1_zfmisc_1(X16))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).
% 0.20/0.46  fof(c_0_7, plain, ![X15]:(~l1_pre_topc(X15)|m1_subset_1(u1_pre_topc(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.20/0.46  fof(c_0_8, plain, ![X5]:(~l1_pre_topc(X5)|(~v1_pre_topc(X5)|X5=g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).
% 0.20/0.46  fof(c_0_9, plain, ![X13, X14]:((v1_pre_topc(g1_pre_topc(X13,X14))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))))&(l1_pre_topc(g1_pre_topc(X13,X14))|~m1_subset_1(X14,k1_zfmisc_1(k1_zfmisc_1(X13))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.20/0.46  cnf(c_0_10, plain, (X1=X2|g1_pre_topc(X1,X3)!=g1_pre_topc(X2,X4)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.46  cnf(c_0_11, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_7])).
% 0.20/0.46  cnf(c_0_12, plain, (X1=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)|~v1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_8])).
% 0.20/0.46  cnf(c_0_13, plain, (v1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.46  cnf(c_0_14, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_9])).
% 0.20/0.46  cnf(c_0_15, plain, (u1_struct_0(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X2,X3)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_10, c_0_11])).
% 0.20/0.46  cnf(c_0_16, plain, (g1_pre_topc(u1_struct_0(g1_pre_topc(X1,X2)),u1_pre_topc(g1_pre_topc(X1,X2)))=g1_pre_topc(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14])).
% 0.20/0.46  fof(c_0_17, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>v2_pre_topc(X1)))), inference(assume_negation,[status(cth)],[t58_pre_topc])).
% 0.20/0.46  cnf(c_0_18, plain, (X1=X2|g1_pre_topc(X3,X1)!=g1_pre_topc(X4,X2)|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3)))), inference(split_conjunct,[status(thm)],[c_0_6])).
% 0.20/0.46  cnf(c_0_19, plain, (u1_struct_0(X1)=u1_struct_0(g1_pre_topc(X2,X3))|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_15, c_0_16])).
% 0.20/0.46  fof(c_0_20, negated_conjecture, (l1_pre_topc(esk4_0)&(v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))&~v2_pre_topc(esk4_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).
% 0.20/0.46  cnf(c_0_21, plain, (u1_pre_topc(X1)=X2|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X3,X2)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_18, c_0_11])).
% 0.20/0.46  cnf(c_0_22, plain, (u1_struct_0(X1)=u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_19, c_0_11])).
% 0.20/0.46  cnf(c_0_23, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_24, plain, (u1_pre_topc(X1)=u1_pre_topc(g1_pre_topc(X2,X3))|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(X2,X3)|~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_21, c_0_16])).
% 0.20/0.46  cnf(c_0_25, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.46  cnf(c_0_26, plain, (u1_pre_topc(X1)=u1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))!=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_24, c_0_11])).
% 0.20/0.46  cnf(c_0_27, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))=u1_struct_0(esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))!=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_25, c_0_25])).
% 0.20/0.46  cnf(c_0_28, negated_conjecture, (u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_pre_topc(esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_26, c_0_23])).
% 0.20/0.46  cnf(c_0_29, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.46  cnf(c_0_30, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))!=g1_pre_topc(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_16]), c_0_14])).
% 0.20/0.46  cnf(c_0_31, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_30, c_0_11])).
% 0.20/0.46  fof(c_0_32, plain, ![X6, X7, X8, X9]:((((r2_hidden(u1_struct_0(X6),u1_pre_topc(X6))|~v2_pre_topc(X6)|~l1_pre_topc(X6))&(~m1_subset_1(X7,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))|(~r1_tarski(X7,u1_pre_topc(X6))|r2_hidden(k5_setfam_1(u1_struct_0(X6),X7),u1_pre_topc(X6)))|~v2_pre_topc(X6)|~l1_pre_topc(X6)))&(~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))|(~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X6)))|(~r2_hidden(X8,u1_pre_topc(X6))|~r2_hidden(X9,u1_pre_topc(X6))|r2_hidden(k9_subset_1(u1_struct_0(X6),X8,X9),u1_pre_topc(X6))))|~v2_pre_topc(X6)|~l1_pre_topc(X6)))&(((m1_subset_1(esk2_1(X6),k1_zfmisc_1(u1_struct_0(X6)))|(m1_subset_1(esk1_1(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6))&((m1_subset_1(esk3_1(X6),k1_zfmisc_1(u1_struct_0(X6)))|(m1_subset_1(esk1_1(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6))&(((r2_hidden(esk2_1(X6),u1_pre_topc(X6))|(m1_subset_1(esk1_1(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6))&(r2_hidden(esk3_1(X6),u1_pre_topc(X6))|(m1_subset_1(esk1_1(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6)))&(~r2_hidden(k9_subset_1(u1_struct_0(X6),esk2_1(X6),esk3_1(X6)),u1_pre_topc(X6))|(m1_subset_1(esk1_1(X6),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X6))))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6)))))&(((m1_subset_1(esk2_1(X6),k1_zfmisc_1(u1_struct_0(X6)))|(r1_tarski(esk1_1(X6),u1_pre_topc(X6))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6))&((m1_subset_1(esk3_1(X6),k1_zfmisc_1(u1_struct_0(X6)))|(r1_tarski(esk1_1(X6),u1_pre_topc(X6))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6))&(((r2_hidden(esk2_1(X6),u1_pre_topc(X6))|(r1_tarski(esk1_1(X6),u1_pre_topc(X6))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6))&(r2_hidden(esk3_1(X6),u1_pre_topc(X6))|(r1_tarski(esk1_1(X6),u1_pre_topc(X6))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6)))&(~r2_hidden(k9_subset_1(u1_struct_0(X6),esk2_1(X6),esk3_1(X6)),u1_pre_topc(X6))|(r1_tarski(esk1_1(X6),u1_pre_topc(X6))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6)))))&((m1_subset_1(esk2_1(X6),k1_zfmisc_1(u1_struct_0(X6)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X6),esk1_1(X6)),u1_pre_topc(X6))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6))&((m1_subset_1(esk3_1(X6),k1_zfmisc_1(u1_struct_0(X6)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X6),esk1_1(X6)),u1_pre_topc(X6))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6))&(((r2_hidden(esk2_1(X6),u1_pre_topc(X6))|(~r2_hidden(k5_setfam_1(u1_struct_0(X6),esk1_1(X6)),u1_pre_topc(X6))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6))&(r2_hidden(esk3_1(X6),u1_pre_topc(X6))|(~r2_hidden(k5_setfam_1(u1_struct_0(X6),esk1_1(X6)),u1_pre_topc(X6))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6)))&(~r2_hidden(k9_subset_1(u1_struct_0(X6),esk2_1(X6),esk3_1(X6)),u1_pre_topc(X6))|(~r2_hidden(k5_setfam_1(u1_struct_0(X6),esk1_1(X6)),u1_pre_topc(X6))|~r2_hidden(u1_struct_0(X6),u1_pre_topc(X6)))|v2_pre_topc(X6)|~l1_pre_topc(X6)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.20/0.46  cnf(c_0_33, negated_conjecture, (u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(er,[status(thm)],[c_0_31]), c_0_23])])).
% 0.20/0.46  cnf(c_0_34, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_35, negated_conjecture, (v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_36, negated_conjecture, (u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))))=u1_pre_topc(esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))!=g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(spm,[status(thm)],[c_0_28, c_0_33])).
% 0.20/0.46  cnf(c_0_37, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_35])])).
% 0.20/0.46  cnf(c_0_38, negated_conjecture, (u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_pre_topc(esk4_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_28]), c_0_23])])).
% 0.20/0.46  cnf(c_0_39, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_28]), c_0_23])])).
% 0.20/0.46  cnf(c_0_40, negated_conjecture, (u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_pre_topc(esk4_0)|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_38, c_0_14])).
% 0.20/0.46  cnf(c_0_41, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_39, c_0_14])).
% 0.20/0.46  cnf(c_0_42, plain, (r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))|~r1_tarski(X1,u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_43, negated_conjecture, (u1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))=u1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_11]), c_0_23])])).
% 0.20/0.46  cnf(c_0_44, plain, (r2_hidden(esk3_1(X1),u1_pre_topc(X1))|m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|v2_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_45, negated_conjecture, (r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_11]), c_0_23])])).
% 0.20/0.46  cnf(c_0_46, negated_conjecture, (~v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.46  cnf(c_0_47, plain, (r2_hidden(esk3_1(X1),u1_pre_topc(X1))|r1_tarski(esk1_1(X1),u1_pre_topc(X1))|v2_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_48, plain, (r2_hidden(esk2_1(X1),u1_pre_topc(X1))|m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|v2_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_49, plain, (r2_hidden(esk2_1(X1),u1_pre_topc(X1))|r1_tarski(esk1_1(X1),u1_pre_topc(X1))|v2_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_50, plain, (r2_hidden(esk3_1(X1),u1_pre_topc(X1))|v2_pre_topc(X1)|~r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_51, negated_conjecture, (r2_hidden(k5_setfam_1(u1_struct_0(esk4_0),X1),u1_pre_topc(esk4_0))|~r1_tarski(X1,u1_pre_topc(esk4_0))|~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_33]), c_0_35])]), c_0_43]), c_0_43])).
% 0.20/0.46  cnf(c_0_52, negated_conjecture, (m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))|r2_hidden(esk3_1(esk4_0),u1_pre_topc(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_23])]), c_0_46])).
% 0.20/0.46  cnf(c_0_53, negated_conjecture, (r1_tarski(esk1_1(esk4_0),u1_pre_topc(esk4_0))|r2_hidden(esk3_1(esk4_0),u1_pre_topc(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_45]), c_0_23])]), c_0_46])).
% 0.20/0.46  cnf(c_0_54, plain, (r2_hidden(esk2_1(X1),u1_pre_topc(X1))|v2_pre_topc(X1)|~r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))|r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_45]), c_0_23])]), c_0_46])).
% 0.20/0.46  cnf(c_0_56, negated_conjecture, (r1_tarski(esk1_1(esk4_0),u1_pre_topc(esk4_0))|r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_45]), c_0_23])]), c_0_46])).
% 0.20/0.46  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_1(esk4_0),u1_pre_topc(esk4_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_51]), c_0_45]), c_0_23])]), c_0_46]), c_0_52]), c_0_53])).
% 0.20/0.46  cnf(c_0_58, negated_conjecture, (r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_51]), c_0_45]), c_0_23])]), c_0_46]), c_0_55]), c_0_56])).
% 0.20/0.46  cnf(c_0_59, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|v2_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_60, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|r1_tarski(esk1_1(X1),u1_pre_topc(X1))|v2_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_61, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|v2_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_62, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|r1_tarski(esk1_1(X1),u1_pre_topc(X1))|v2_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_63, plain, (r2_hidden(k9_subset_1(u1_struct_0(X2),X1,X3),u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,u1_pre_topc(X2))|~r2_hidden(X3,u1_pre_topc(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_64, negated_conjecture, (r2_hidden(esk3_1(esk4_0),u1_pre_topc(esk4_0))|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_57, c_0_14])).
% 0.20/0.46  cnf(c_0_65, negated_conjecture, (r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0))|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_58, c_0_14])).
% 0.20/0.46  cnf(c_0_66, plain, (m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_pre_topc(X1)|~r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_67, negated_conjecture, (m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))|m1_subset_1(esk2_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_45]), c_0_23])]), c_0_46])).
% 0.20/0.46  cnf(c_0_68, negated_conjecture, (r1_tarski(esk1_1(esk4_0),u1_pre_topc(esk4_0))|m1_subset_1(esk2_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_45]), c_0_23])]), c_0_46])).
% 0.20/0.46  cnf(c_0_69, plain, (m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_pre_topc(X1)|~r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))|m1_subset_1(esk3_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_45]), c_0_23])]), c_0_46])).
% 0.20/0.46  cnf(c_0_71, negated_conjecture, (r1_tarski(esk1_1(esk4_0),u1_pre_topc(esk4_0))|m1_subset_1(esk3_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_45]), c_0_23])]), c_0_46])).
% 0.20/0.46  cnf(c_0_72, plain, (v2_pre_topc(X1)|~r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))|~r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_73, negated_conjecture, (r2_hidden(k9_subset_1(u1_struct_0(esk4_0),X1,X2),u1_pre_topc(esk4_0))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(X2,u1_pre_topc(esk4_0))|~r2_hidden(X1,u1_pre_topc(esk4_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_33]), c_0_35])]), c_0_43]), c_0_43]), c_0_43])).
% 0.20/0.46  cnf(c_0_74, negated_conjecture, (r2_hidden(esk3_1(esk4_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_11]), c_0_23])])).
% 0.20/0.46  cnf(c_0_75, negated_conjecture, (r2_hidden(esk2_1(esk4_0),u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_11]), c_0_23])])).
% 0.20/0.46  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk2_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_51]), c_0_45]), c_0_23])]), c_0_46]), c_0_67]), c_0_68])).
% 0.20/0.46  cnf(c_0_77, negated_conjecture, (m1_subset_1(esk3_1(esk4_0),k1_zfmisc_1(u1_struct_0(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_51]), c_0_45]), c_0_23])]), c_0_46]), c_0_70]), c_0_71])).
% 0.20/0.46  cnf(c_0_78, plain, (r1_tarski(esk1_1(X1),u1_pre_topc(X1))|v2_pre_topc(X1)|~r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_79, negated_conjecture, (~r2_hidden(k5_setfam_1(u1_struct_0(esk4_0),esk1_1(esk4_0)),u1_pre_topc(esk4_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_45]), c_0_23]), c_0_74]), c_0_75])]), c_0_46]), c_0_76]), c_0_77])).
% 0.20/0.46  cnf(c_0_80, negated_conjecture, (r1_tarski(esk1_1(esk4_0),u1_pre_topc(esk4_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_73]), c_0_45]), c_0_23]), c_0_74]), c_0_75])]), c_0_46]), c_0_68]), c_0_71])).
% 0.20/0.46  cnf(c_0_81, plain, (m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|v2_pre_topc(X1)|~r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 0.20/0.46  cnf(c_0_82, negated_conjecture, (~m1_subset_1(esk1_1(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_51]), c_0_80])).
% 0.20/0.46  cnf(c_0_83, negated_conjecture, (~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_73]), c_0_45]), c_0_23]), c_0_74]), c_0_75])]), c_0_46]), c_0_67]), c_0_70]), c_0_82])).
% 0.20/0.46  cnf(c_0_84, negated_conjecture, (~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_83, c_0_14])).
% 0.20/0.46  cnf(c_0_85, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_11]), c_0_23])]), ['proof']).
% 0.20/0.46  # SZS output end CNFRefutation
% 0.20/0.46  # Proof object total steps             : 86
% 0.20/0.46  # Proof object clause steps            : 73
% 0.20/0.46  # Proof object formula steps           : 13
% 0.20/0.46  # Proof object conjectures             : 45
% 0.20/0.46  # Proof object clause conjectures      : 42
% 0.20/0.46  # Proof object formula conjectures     : 3
% 0.20/0.46  # Proof object initial clauses used    : 27
% 0.20/0.46  # Proof object initial formulas used   : 6
% 0.20/0.46  # Proof object generating inferences   : 46
% 0.20/0.46  # Proof object simplifying inferences  : 103
% 0.20/0.46  # Training examples: 0 positive, 0 negative
% 0.20/0.46  # Parsed axioms                        : 6
% 0.20/0.46  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.46  # Initial clauses                      : 27
% 0.20/0.46  # Removed in clause preprocessing      : 0
% 0.20/0.46  # Initial clauses in saturation        : 27
% 0.20/0.46  # Processed clauses                    : 482
% 0.20/0.46  # ...of these trivial                  : 4
% 0.20/0.46  # ...subsumed                          : 234
% 0.20/0.46  # ...remaining for further processing  : 244
% 0.20/0.46  # Other redundant clauses eliminated   : 0
% 0.20/0.46  # Clauses deleted for lack of memory   : 0
% 0.20/0.46  # Backward-subsumed                    : 29
% 0.20/0.46  # Backward-rewritten                   : 79
% 0.20/0.46  # Generated clauses                    : 2314
% 0.20/0.46  # ...of the previous two non-trivial   : 2101
% 0.20/0.46  # Contextual simplify-reflections      : 44
% 0.20/0.46  # Paramodulations                      : 2279
% 0.20/0.46  # Factorizations                       : 0
% 0.20/0.46  # Equation resolutions                 : 35
% 0.20/0.46  # Propositional unsat checks           : 0
% 0.20/0.46  #    Propositional check models        : 0
% 0.20/0.46  #    Propositional check unsatisfiable : 0
% 0.20/0.46  #    Propositional clauses             : 0
% 0.20/0.46  #    Propositional clauses after purity: 0
% 0.20/0.46  #    Propositional unsat core size     : 0
% 0.20/0.46  #    Propositional preprocessing time  : 0.000
% 0.20/0.46  #    Propositional encoding time       : 0.000
% 0.20/0.46  #    Propositional solver time         : 0.000
% 0.20/0.46  #    Success case prop preproc time    : 0.000
% 0.20/0.46  #    Success case prop encoding time   : 0.000
% 0.20/0.46  #    Success case prop solver time     : 0.000
% 0.20/0.46  # Current number of processed clauses  : 109
% 0.20/0.46  #    Positive orientable unit clauses  : 7
% 0.20/0.46  #    Positive unorientable unit clauses: 0
% 0.20/0.46  #    Negative unit clauses             : 3
% 0.20/0.46  #    Non-unit-clauses                  : 99
% 0.20/0.46  # Current number of unprocessed clauses: 1513
% 0.20/0.46  # ...number of literals in the above   : 11829
% 0.20/0.46  # Current number of archived formulas  : 0
% 0.20/0.46  # Current number of archived clauses   : 135
% 0.20/0.46  # Clause-clause subsumption calls (NU) : 13904
% 0.20/0.46  # Rec. Clause-clause subsumption calls : 2614
% 0.20/0.46  # Non-unit clause-clause subsumptions  : 306
% 0.20/0.46  # Unit Clause-clause subsumption calls : 146
% 0.20/0.46  # Rewrite failures with RHS unbound    : 0
% 0.20/0.46  # BW rewrite match attempts            : 11
% 0.20/0.46  # BW rewrite match successes           : 5
% 0.20/0.46  # Condensation attempts                : 0
% 0.20/0.46  # Condensation successes               : 0
% 0.20/0.46  # Termbank termtop insertions          : 184131
% 0.20/0.46  
% 0.20/0.46  # -------------------------------------------------
% 0.20/0.46  # User time                : 0.115 s
% 0.20/0.46  # System time              : 0.005 s
% 0.20/0.46  # Total time               : 0.120 s
% 0.20/0.46  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
