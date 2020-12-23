%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1127+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:46 EST 2020

% Result     : Theorem 0.64s
% Output     : CNFRefutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   94 (13320 expanded)
%              Number of clauses        :   81 (5995 expanded)
%              Number of leaves         :    6 (3392 expanded)
%              Depth                    :   25
%              Number of atoms          :  385 (44929 expanded)
%              Number of equality atoms :   58 (9037 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :   10 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(free_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ! [X3,X4] :
          ( g1_pre_topc(X1,X2) = g1_pre_topc(X3,X4)
         => ( X1 = X3
            & X2 = X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(t58_pre_topc,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
       => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(c_0_6,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X17 = X19
        | g1_pre_topc(X17,X18) != g1_pre_topc(X19,X20)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( X18 = X20
        | g1_pre_topc(X17,X18) != g1_pre_topc(X19,X20)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) ) ) ),
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
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
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
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
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
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

cnf(c_0_19,plain,
    ( u1_pre_topc(X1) = u1_pre_topc(g1_pre_topc(X2,X3))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_15,c_0_16])).

fof(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    & ~ v2_pre_topc(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_17])])])).

cnf(c_0_21,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_11])).

cnf(c_0_22,plain,
    ( u1_pre_topc(X1) = u1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_19,c_0_11])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,plain,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = X3
    | g1_pre_topc(X1,X2) != g1_pre_topc(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_16]),c_0_14])).

cnf(c_0_25,plain,
    ( u1_pre_topc(g1_pre_topc(X1,X2)) = X3
    | g1_pre_topc(X1,X2) != g1_pre_topc(X4,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_pre_topc(esk5_0)
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_27,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_11])).

cnf(c_0_28,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_11])).

cnf(c_0_29,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(esk5_0))) = u1_pre_topc(esk5_0)
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_26])).

cnf(c_0_30,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_31,plain,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_28])).

cnf(c_0_32,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0))) = u1_pre_topc(esk5_0)
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_29])).

cnf(c_0_33,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(X1))) = u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_31])).

cnf(c_0_34,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0))) = u1_pre_topc(esk5_0)
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_23])])).

cnf(c_0_35,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0))) = u1_pre_topc(esk5_0)
    | g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_23])])).

fof(c_0_36,plain,(
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

cnf(c_0_37,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = u1_pre_topc(esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_23])])).

cnf(c_0_38,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_39,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = u1_pre_topc(esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_14])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(esk5_0))
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_41,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) = u1_struct_0(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_30,c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( u1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = u1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_11]),c_0_23])])).

cnf(c_0_43,negated_conjecture,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(esk5_0))
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_40,c_0_30])).

cnf(c_0_44,negated_conjecture,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = u1_struct_0(esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_23])])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_23])])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = u1_struct_0(esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_14])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_46,c_0_14])).

cnf(c_0_49,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_50,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) = u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_11]),c_0_23])])).

cnf(c_0_51,plain,
    ( r2_hidden(esk3_1(X1),u1_pre_topc(X1))
    | m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_52,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_11]),c_0_23])])).

cnf(c_0_53,negated_conjecture,
    ( ~ v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_54,plain,
    ( r2_hidden(esk3_1(X1),u1_pre_topc(X1))
    | r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_55,plain,
    ( r2_hidden(esk2_1(X1),u1_pre_topc(X1))
    | m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_56,plain,
    ( r2_hidden(esk2_1(X1),u1_pre_topc(X1))
    | r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_57,plain,
    ( r2_hidden(esk3_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(k5_setfam_1(u1_struct_0(esk5_0),X1),u1_pre_topc(esk5_0))
    | ~ r1_tarski(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_42]),c_0_42]),c_0_44])])).

cnf(c_0_59,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | r2_hidden(esk3_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_23])]),c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(esk1_1(esk5_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk3_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_52]),c_0_23])]),c_0_53])).

cnf(c_0_61,plain,
    ( r2_hidden(esk2_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | r2_hidden(esk2_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_52]),c_0_23])]),c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk1_1(esk5_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk2_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_52]),c_0_23])]),c_0_53])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_1(esk5_0),u1_pre_topc(esk5_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_52]),c_0_23])]),c_0_53]),c_0_59]),c_0_60])).

cnf(c_0_65,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),u1_pre_topc(esk5_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_58]),c_0_52]),c_0_23])]),c_0_53]),c_0_62]),c_0_63])).

cnf(c_0_66,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_67,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_68,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_69,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_70,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X2),X1,X3),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk3_1(esk5_0),u1_pre_topc(esk5_0))
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_14])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),u1_pre_topc(esk5_0))
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_65,c_0_14])).

cnf(c_0_73,plain,
    ( m1_subset_1(esk2_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_74,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | m1_subset_1(esk2_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_52]),c_0_23])]),c_0_53])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(esk1_1(esk5_0),u1_pre_topc(esk5_0))
    | m1_subset_1(esk2_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_52]),c_0_23])]),c_0_53])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk3_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | m1_subset_1(esk3_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_52]),c_0_23])]),c_0_53])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(esk1_1(esk5_0),u1_pre_topc(esk5_0))
    | m1_subset_1(esk3_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_52]),c_0_23])]),c_0_53])).

cnf(c_0_79,plain,
    ( v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk5_0),X1,X2),u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X2,u1_pre_topc(esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_50]),c_0_42]),c_0_42]),c_0_42]),c_0_44])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk3_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_11]),c_0_23])])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_11]),c_0_23])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk2_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_58]),c_0_52]),c_0_23])]),c_0_53]),c_0_74]),c_0_75])).

cnf(c_0_84,negated_conjecture,
    ( m1_subset_1(esk3_1(esk5_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_58]),c_0_52]),c_0_23])]),c_0_53]),c_0_77]),c_0_78])).

cnf(c_0_85,negated_conjecture,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(esk5_0),esk1_1(esk5_0)),u1_pre_topc(esk5_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_52]),c_0_23]),c_0_81]),c_0_82])]),c_0_53]),c_0_83]),c_0_84])).

cnf(c_0_86,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_87,plain,
    ( r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_88,negated_conjecture,
    ( ~ r1_tarski(esk1_1(esk5_0),u1_pre_topc(esk5_0))
    | ~ m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_85,c_0_58])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_80]),c_0_52]),c_0_23]),c_0_81]),c_0_82])]),c_0_53]),c_0_74]),c_0_77])).

cnf(c_0_90,negated_conjecture,
    ( r1_tarski(esk1_1(esk5_0),u1_pre_topc(esk5_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_80]),c_0_52]),c_0_23]),c_0_81]),c_0_82])]),c_0_53]),c_0_75]),c_0_78])).

cnf(c_0_91,negated_conjecture,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_92,negated_conjecture,
    ( ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_91,c_0_14])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_11]),c_0_23])]),
    [proof]).

%------------------------------------------------------------------------------
