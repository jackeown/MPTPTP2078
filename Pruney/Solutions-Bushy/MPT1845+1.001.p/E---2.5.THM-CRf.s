%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1845+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:53 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   55 (3953 expanded)
%              Number of clauses        :   44 (1625 expanded)
%              Number of leaves         :    5 ( 922 expanded)
%              Depth                    :   14
%              Number of atoms          :  249 (18071 expanded)
%              Number of equality atoms :   24 (4207 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

fof(t12_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & v2_pre_topc(X1) )
           => v2_pre_topc(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tex_2)).

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

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_5,plain,(
    ! [X17,X18,X19,X20] :
      ( ( X17 = X19
        | g1_pre_topc(X17,X18) != g1_pre_topc(X19,X20)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) )
      & ( X18 = X20
        | g1_pre_topc(X17,X18) != g1_pre_topc(X19,X20)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k1_zfmisc_1(X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_6,plain,(
    ! [X15] :
      ( ~ l1_pre_topc(X15)
      | m1_subset_1(u1_pre_topc(X15),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X15)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_7,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( l1_pre_topc(X2)
           => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & v2_pre_topc(X1) )
             => v2_pre_topc(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_tex_2])).

cnf(c_0_8,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_9,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_6])).

fof(c_0_10,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & l1_pre_topc(esk5_0)
    & g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    & v2_pre_topc(esk4_0)
    & ~ v2_pre_topc(esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_7])])])).

cnf(c_0_11,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_8,c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( u1_pre_topc(esk4_0) = X1
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(X2,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13])])).

cnf(c_0_15,negated_conjecture,
    ( u1_pre_topc(esk4_0) = u1_pre_topc(esk5_0) ),
    inference(er,[status(thm)],[c_0_14])).

fof(c_0_16,plain,(
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

cnf(c_0_17,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_5])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_9,c_0_15]),c_0_13])])).

cnf(c_0_19,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk5_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_12,c_0_15])).

fof(c_0_20,plain,(
    ! [X23,X24,X25] :
      ( ~ r2_hidden(X23,X24)
      | ~ m1_subset_1(X24,k1_zfmisc_1(X25))
      | m1_subset_1(X23,X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_21,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( u1_struct_0(esk4_0) = X1
    | g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) != g1_pre_topc(X1,X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk4_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_21,c_0_15]),c_0_22]),c_0_13])])).

cnf(c_0_26,negated_conjecture,
    ( u1_struct_0(esk4_0) = u1_struct_0(esk5_0) ),
    inference(er,[status(thm)],[c_0_23])).

cnf(c_0_27,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_24,c_0_18])).

cnf(c_0_28,plain,
    ( r2_hidden(k5_setfam_1(u1_struct_0(X2),X1),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
    | ~ r1_tarski(X1,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,plain,
    ( r2_hidden(esk3_1(X1),u1_pre_topc(X1))
    | m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( r2_hidden(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_33,plain,
    ( r2_hidden(esk3_1(X1),u1_pre_topc(X1))
    | r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_34,plain,
    ( r2_hidden(esk2_1(X1),u1_pre_topc(X1))
    | m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( r2_hidden(esk2_1(X1),u1_pre_topc(X1))
    | r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_36,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X2),X1,X3),u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_26])).

cnf(c_0_38,plain,
    ( r2_hidden(esk3_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k5_setfam_1(u1_struct_0(esk5_0),X1),u1_pre_topc(esk5_0))
    | ~ r1_tarski(X1,u1_pre_topc(esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_15]),c_0_22]),c_0_13])]),c_0_26]),c_0_26])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | r2_hidden(esk3_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_41,negated_conjecture,
    ( r1_tarski(esk1_1(esk5_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk3_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_42,plain,
    ( r2_hidden(esk2_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))
    | r2_hidden(esk2_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk1_1(esk5_0),u1_pre_topc(esk5_0))
    | r2_hidden(esk2_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_45,plain,
    ( v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(k5_setfam_1(u1_struct_0(X1),esk1_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk5_0),X1,X2),u1_pre_topc(esk5_0))
    | ~ r2_hidden(X2,u1_pre_topc(esk5_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_15]),c_0_22]),c_0_13])]),c_0_26]),c_0_26]),c_0_26]),c_0_37]),c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk3_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_30]),c_0_31])]),c_0_32]),c_0_40]),c_0_41])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk2_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_39]),c_0_30]),c_0_31])]),c_0_32]),c_0_43]),c_0_44])).

cnf(c_0_49,plain,
    ( r1_tarski(esk1_1(X1),u1_pre_topc(X1))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_50,negated_conjecture,
    ( ~ r2_hidden(k5_setfam_1(u1_struct_0(esk5_0),esk1_1(esk5_0)),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_30]),c_0_31]),c_0_47]),c_0_48])]),c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk1_1(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_46]),c_0_30]),c_0_31]),c_0_47]),c_0_48])]),c_0_32])).

cnf(c_0_52,plain,
    ( m1_subset_1(esk1_1(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | v2_pre_topc(X1)
    | ~ r2_hidden(k9_subset_1(u1_struct_0(X1),esk2_1(X1),esk3_1(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( ~ m1_subset_1(esk1_1(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_39]),c_0_51])])).

cnf(c_0_54,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_46]),c_0_30]),c_0_31]),c_0_47]),c_0_48])]),c_0_32]),c_0_53]),
    [proof]).

%------------------------------------------------------------------------------
