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
% DateTime   : Thu Dec  3 11:18:15 EST 2020

% Result     : Theorem 0.14s
% Output     : CNFRefutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 495 expanded)
%              Number of clauses        :   38 ( 184 expanded)
%              Number of leaves         :   10 ( 122 expanded)
%              Depth                    :   12
%              Number of atoms          :  282 (2765 expanded)
%              Number of equality atoms :   38 ( 404 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t103_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r2_hidden(X2,u1_pre_topc(X1))
          <=> u1_pre_topc(X1) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

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

fof(t106_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(d9_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(t104_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( u1_struct_0(k6_tmap_1(X1,X2)) = u1_struct_0(X1)
            & u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(c_0_10,plain,(
    ! [X6,X7,X8] :
      ( ~ r2_hidden(X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8))
      | m1_subset_1(X6,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_11,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | m1_subset_1(u1_pre_topc(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_12,plain,(
    ! [X21,X22] :
      ( ( ~ r2_hidden(X22,u1_pre_topc(X21))
        | u1_pre_topc(X21) = k5_tmap_1(X21,X22)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( u1_pre_topc(X21) != k5_tmap_1(X21,X22)
        | r2_hidden(X22,u1_pre_topc(X21))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | v2_struct_0(X21)
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).

cnf(c_0_13,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,plain,(
    ! [X5] : m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_16,plain,(
    ! [X4] : k2_subset_1(X4) = X4 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_17,plain,
    ( u1_pre_topc(X2) = k5_tmap_1(X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

fof(c_0_19,plain,(
    ! [X9,X10,X11,X12] :
      ( ( r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r1_tarski(X10,u1_pre_topc(X9))
        | r2_hidden(k5_setfam_1(u1_struct_0(X9),X10),u1_pre_topc(X9))
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ r2_hidden(X11,u1_pre_topc(X9))
        | ~ r2_hidden(X12,u1_pre_topc(X9))
        | r2_hidden(k9_subset_1(u1_struct_0(X9),X11,X12),u1_pre_topc(X9))
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk2_1(X9),u1_pre_topc(X9))
        | m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk3_1(X9),u1_pre_topc(X9))
        | m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))
        | m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | r1_tarski(esk1_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | r1_tarski(esk1_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk2_1(X9),u1_pre_topc(X9))
        | r1_tarski(esk1_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk3_1(X9),u1_pre_topc(X9))
        | r1_tarski(esk1_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))
        | r1_tarski(esk1_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk2_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk3_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( v3_pre_topc(X2,X1)
            <=> g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k6_tmap_1(X1,X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t106_tmap_1])).

fof(c_0_21,plain,(
    ! [X19,X20] :
      ( v2_struct_0(X19)
      | ~ v2_pre_topc(X19)
      | ~ l1_pre_topc(X19)
      | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))
      | k6_tmap_1(X19,X20) = g1_pre_topc(u1_struct_0(X19),k5_tmap_1(X19,X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).

cnf(c_0_22,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_23,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_24,plain,
    ( k5_tmap_1(X1,X2) = u1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(X2,u1_pre_topc(X1)) ),
    inference(csr,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_25,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v3_pre_topc(esk5_0,esk4_0)
      | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != k6_tmap_1(esk4_0,esk5_0) )
    & ( v3_pre_topc(esk5_0,esk4_0)
      | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = k6_tmap_1(esk4_0,esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | k6_tmap_1(X1,X2) = g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( k5_tmap_1(X1,u1_struct_0(X1)) = u1_pre_topc(X1)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X23,X24] :
      ( ( u1_struct_0(k6_tmap_1(X23,X24)) = u1_struct_0(X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( u1_pre_topc(k6_tmap_1(X23,X24)) = k5_tmap_1(X23,X24)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))
        | v2_struct_0(X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).

cnf(c_0_34,plain,
    ( g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,u1_struct_0(X1))) = k6_tmap_1(X1,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( k5_tmap_1(esk4_0,u1_struct_0(esk4_0)) = u1_pre_topc(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_36,plain,
    ( u1_pre_topc(k6_tmap_1(X1,X2)) = k5_tmap_1(X1,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_37,plain,(
    ! [X16,X17] :
      ( ( ~ v3_pre_topc(X17,X16)
        | r2_hidden(X17,u1_pre_topc(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( ~ r2_hidden(X17,u1_pre_topc(X16))
        | v3_pre_topc(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_38,negated_conjecture,
    ( v3_pre_topc(esk5_0,esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = k6_tmap_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) = k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_30]),c_0_35]),c_0_31])]),c_0_32])).

cnf(c_0_40,plain,
    ( u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1))) = k5_tmap_1(X1,u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_28])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k6_tmap_1(esk4_0,esk5_0)
    | v3_pre_topc(esk5_0,esk4_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_44,plain,
    ( r2_hidden(X2,u1_pre_topc(X1))
    | v2_struct_0(X1)
    | u1_pre_topc(X1) != k5_tmap_1(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( ~ v3_pre_topc(esk5_0,esk4_0)
    | g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)) != k6_tmap_1(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_46,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0))) = u1_pre_topc(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_30]),c_0_35]),c_0_31])]),c_0_32])).

cnf(c_0_48,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) = k6_tmap_1(esk4_0,esk5_0)
    | r2_hidden(esk5_0,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_31]),c_0_43])])).

cnf(c_0_49,negated_conjecture,
    ( u1_pre_topc(k6_tmap_1(esk4_0,esk5_0)) = k5_tmap_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_43]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(esk5_0,u1_pre_topc(esk4_0))
    | k5_tmap_1(esk4_0,esk5_0) != u1_pre_topc(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_43]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_51,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) != k6_tmap_1(esk4_0,esk5_0)
    | ~ v3_pre_topc(esk5_0,esk4_0) ),
    inference(rw,[status(thm)],[c_0_45,c_0_39])).

cnf(c_0_52,plain,
    ( v3_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(csr,[status(thm)],[c_0_46,c_0_18])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk5_0,u1_pre_topc(esk4_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) != k6_tmap_1(esk4_0,esk5_0)
    | ~ r2_hidden(esk5_0,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_31])])).

cnf(c_0_55,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,esk5_0)) = k6_tmap_1(esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_43]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_56,negated_conjecture,
    ( k5_tmap_1(esk4_0,esk5_0) = u1_pre_topc(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_53]),c_0_30]),c_0_31])]),c_0_32])).

cnf(c_0_57,negated_conjecture,
    ( k6_tmap_1(esk4_0,u1_struct_0(esk4_0)) != k6_tmap_1(esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54,c_0_53])])).

cnf(c_0_58,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55,c_0_56]),c_0_39]),c_0_57]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:18:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.14/0.38  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.14/0.38  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.14/0.38  #
% 0.14/0.38  # Preprocessing time       : 0.028 s
% 0.14/0.38  # Presaturation interreduction done
% 0.14/0.38  
% 0.14/0.38  # Proof found!
% 0.14/0.38  # SZS status Theorem
% 0.14/0.38  # SZS output start CNFRefutation
% 0.14/0.38  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.14/0.38  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.14/0.38  fof(t103_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(r2_hidden(X2,u1_pre_topc(X1))<=>u1_pre_topc(X1)=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_tmap_1)).
% 0.14/0.38  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.14/0.38  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.14/0.38  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.14/0.38  fof(t106_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_tmap_1)).
% 0.14/0.38  fof(d9_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_tmap_1)).
% 0.14/0.38  fof(t104_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(u1_struct_0(k6_tmap_1(X1,X2))=u1_struct_0(X1)&u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t104_tmap_1)).
% 0.14/0.38  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.14/0.38  fof(c_0_10, plain, ![X6, X7, X8]:(~r2_hidden(X6,X7)|~m1_subset_1(X7,k1_zfmisc_1(X8))|m1_subset_1(X6,X8)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.14/0.38  fof(c_0_11, plain, ![X18]:(~l1_pre_topc(X18)|m1_subset_1(u1_pre_topc(X18),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X18))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.14/0.38  fof(c_0_12, plain, ![X21, X22]:((~r2_hidden(X22,u1_pre_topc(X21))|u1_pre_topc(X21)=k5_tmap_1(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(u1_pre_topc(X21)!=k5_tmap_1(X21,X22)|r2_hidden(X22,u1_pre_topc(X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t103_tmap_1])])])])])).
% 0.14/0.38  cnf(c_0_13, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.14/0.38  cnf(c_0_14, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.14/0.38  fof(c_0_15, plain, ![X5]:m1_subset_1(k2_subset_1(X5),k1_zfmisc_1(X5)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.14/0.38  fof(c_0_16, plain, ![X4]:k2_subset_1(X4)=X4, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.14/0.38  cnf(c_0_17, plain, (u1_pre_topc(X2)=k5_tmap_1(X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_13, c_0_14])).
% 0.14/0.38  fof(c_0_19, plain, ![X9, X10, X11, X12]:((((r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))|~v2_pre_topc(X9)|~l1_pre_topc(X9))&(~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|(~r1_tarski(X10,u1_pre_topc(X9))|r2_hidden(k5_setfam_1(u1_struct_0(X9),X10),u1_pre_topc(X9)))|~v2_pre_topc(X9)|~l1_pre_topc(X9)))&(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X9)))|(~r2_hidden(X11,u1_pre_topc(X9))|~r2_hidden(X12,u1_pre_topc(X9))|r2_hidden(k9_subset_1(u1_struct_0(X9),X11,X12),u1_pre_topc(X9))))|~v2_pre_topc(X9)|~l1_pre_topc(X9)))&(((m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&((m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(((r2_hidden(esk2_1(X9),u1_pre_topc(X9))|(m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(r2_hidden(esk3_1(X9),u1_pre_topc(X9))|(m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))&(~r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))|(m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))))&(((m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(r1_tarski(esk1_1(X9),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&((m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(r1_tarski(esk1_1(X9),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(((r2_hidden(esk2_1(X9),u1_pre_topc(X9))|(r1_tarski(esk1_1(X9),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(r2_hidden(esk3_1(X9),u1_pre_topc(X9))|(r1_tarski(esk1_1(X9),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))&(~r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))|(r1_tarski(esk1_1(X9),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))))&((m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&((m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(((r2_hidden(esk2_1(X9),u1_pre_topc(X9))|(~r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(r2_hidden(esk3_1(X9),u1_pre_topc(X9))|(~r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))&(~r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))|(~r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.14/0.38  fof(c_0_20, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))=k6_tmap_1(X1,X2))))), inference(assume_negation,[status(cth)],[t106_tmap_1])).
% 0.14/0.38  fof(c_0_21, plain, ![X19, X20]:(v2_struct_0(X19)|~v2_pre_topc(X19)|~l1_pre_topc(X19)|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X19)))|k6_tmap_1(X19,X20)=g1_pre_topc(u1_struct_0(X19),k5_tmap_1(X19,X20)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d9_tmap_1])])])])).
% 0.14/0.38  cnf(c_0_22, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.14/0.38  cnf(c_0_23, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.14/0.38  cnf(c_0_24, plain, (k5_tmap_1(X1,X2)=u1_pre_topc(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~r2_hidden(X2,u1_pre_topc(X1))), inference(csr,[status(thm)],[c_0_17, c_0_18])).
% 0.14/0.38  cnf(c_0_25, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.14/0.38  fof(c_0_26, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))&((~v3_pre_topc(esk5_0,esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))!=k6_tmap_1(esk4_0,esk5_0))&(v3_pre_topc(esk5_0,esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=k6_tmap_1(esk4_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).
% 0.14/0.38  cnf(c_0_27, plain, (v2_struct_0(X1)|k6_tmap_1(X1,X2)=g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.14/0.38  cnf(c_0_28, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_22, c_0_23])).
% 0.14/0.38  cnf(c_0_29, plain, (k5_tmap_1(X1,u1_struct_0(X1))=u1_pre_topc(X1)|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.14/0.38  cnf(c_0_30, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_31, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  fof(c_0_33, plain, ![X23, X24]:((u1_struct_0(k6_tmap_1(X23,X24))=u1_struct_0(X23)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))&(u1_pre_topc(k6_tmap_1(X23,X24))=k5_tmap_1(X23,X24)|~m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X23)))|(v2_struct_0(X23)|~v2_pre_topc(X23)|~l1_pre_topc(X23)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t104_tmap_1])])])])])).
% 0.14/0.38  cnf(c_0_34, plain, (g1_pre_topc(u1_struct_0(X1),k5_tmap_1(X1,u1_struct_0(X1)))=k6_tmap_1(X1,u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.14/0.38  cnf(c_0_35, negated_conjecture, (k5_tmap_1(esk4_0,u1_struct_0(esk4_0))=u1_pre_topc(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])]), c_0_32])).
% 0.14/0.38  cnf(c_0_36, plain, (u1_pre_topc(k6_tmap_1(X1,X2))=k5_tmap_1(X1,X2)|v2_struct_0(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.14/0.38  fof(c_0_37, plain, ![X16, X17]:((~v3_pre_topc(X17,X16)|r2_hidden(X17,u1_pre_topc(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(~r2_hidden(X17,u1_pre_topc(X16))|v3_pre_topc(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.14/0.38  cnf(c_0_38, negated_conjecture, (v3_pre_topc(esk5_0,esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=k6_tmap_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_39, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))=k6_tmap_1(esk4_0,u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_30]), c_0_35]), c_0_31])]), c_0_32])).
% 0.14/0.38  cnf(c_0_40, plain, (u1_pre_topc(k6_tmap_1(X1,u1_struct_0(X1)))=k5_tmap_1(X1,u1_struct_0(X1))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_36, c_0_28])).
% 0.14/0.38  cnf(c_0_41, plain, (r2_hidden(X1,u1_pre_topc(X2))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.38  cnf(c_0_42, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(esk4_0))=k6_tmap_1(esk4_0,esk5_0)|v3_pre_topc(esk5_0,esk4_0)), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.14/0.38  cnf(c_0_43, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_44, plain, (r2_hidden(X2,u1_pre_topc(X1))|v2_struct_0(X1)|u1_pre_topc(X1)!=k5_tmap_1(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.14/0.38  cnf(c_0_45, negated_conjecture, (~v3_pre_topc(esk5_0,esk4_0)|g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))!=k6_tmap_1(esk4_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.14/0.38  cnf(c_0_46, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.14/0.38  cnf(c_0_47, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk4_0,u1_struct_0(esk4_0)))=u1_pre_topc(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_30]), c_0_35]), c_0_31])]), c_0_32])).
% 0.14/0.38  cnf(c_0_48, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(esk4_0))=k6_tmap_1(esk4_0,esk5_0)|r2_hidden(esk5_0,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_31]), c_0_43])])).
% 0.14/0.38  cnf(c_0_49, negated_conjecture, (u1_pre_topc(k6_tmap_1(esk4_0,esk5_0))=k5_tmap_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_43]), c_0_30]), c_0_31])]), c_0_32])).
% 0.14/0.38  cnf(c_0_50, negated_conjecture, (r2_hidden(esk5_0,u1_pre_topc(esk4_0))|k5_tmap_1(esk4_0,esk5_0)!=u1_pre_topc(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_43]), c_0_30]), c_0_31])]), c_0_32])).
% 0.14/0.38  cnf(c_0_51, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(esk4_0))!=k6_tmap_1(esk4_0,esk5_0)|~v3_pre_topc(esk5_0,esk4_0)), inference(rw,[status(thm)],[c_0_45, c_0_39])).
% 0.14/0.38  cnf(c_0_52, plain, (v3_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(csr,[status(thm)],[c_0_46, c_0_18])).
% 0.14/0.38  cnf(c_0_53, negated_conjecture, (r2_hidden(esk5_0,u1_pre_topc(esk4_0))), inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])).
% 0.14/0.38  cnf(c_0_54, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(esk4_0))!=k6_tmap_1(esk4_0,esk5_0)|~r2_hidden(esk5_0,u1_pre_topc(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_31])])).
% 0.14/0.38  cnf(c_0_55, negated_conjecture, (g1_pre_topc(u1_struct_0(esk4_0),k5_tmap_1(esk4_0,esk5_0))=k6_tmap_1(esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27, c_0_43]), c_0_30]), c_0_31])]), c_0_32])).
% 0.14/0.38  cnf(c_0_56, negated_conjecture, (k5_tmap_1(esk4_0,esk5_0)=u1_pre_topc(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_53]), c_0_30]), c_0_31])]), c_0_32])).
% 0.14/0.38  cnf(c_0_57, negated_conjecture, (k6_tmap_1(esk4_0,u1_struct_0(esk4_0))!=k6_tmap_1(esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_54, c_0_53])])).
% 0.14/0.38  cnf(c_0_58, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_55, c_0_56]), c_0_39]), c_0_57]), ['proof']).
% 0.14/0.38  # SZS output end CNFRefutation
% 0.14/0.38  # Proof object total steps             : 59
% 0.14/0.38  # Proof object clause steps            : 38
% 0.14/0.38  # Proof object formula steps           : 21
% 0.14/0.38  # Proof object conjectures             : 23
% 0.14/0.38  # Proof object clause conjectures      : 20
% 0.14/0.38  # Proof object formula conjectures     : 3
% 0.14/0.38  # Proof object initial clauses used    : 17
% 0.14/0.38  # Proof object initial formulas used   : 10
% 0.14/0.38  # Proof object generating inferences   : 15
% 0.14/0.38  # Proof object simplifying inferences  : 43
% 0.14/0.38  # Training examples: 0 positive, 0 negative
% 0.14/0.38  # Parsed axioms                        : 10
% 0.14/0.38  # Removed by relevancy pruning/SinE    : 0
% 0.14/0.38  # Initial clauses                      : 35
% 0.14/0.38  # Removed in clause preprocessing      : 1
% 0.14/0.38  # Initial clauses in saturation        : 34
% 0.14/0.38  # Processed clauses                    : 128
% 0.14/0.38  # ...of these trivial                  : 0
% 0.14/0.38  # ...subsumed                          : 9
% 0.14/0.38  # ...remaining for further processing  : 119
% 0.14/0.38  # Other redundant clauses eliminated   : 0
% 0.14/0.38  # Clauses deleted for lack of memory   : 0
% 0.14/0.38  # Backward-subsumed                    : 0
% 0.14/0.38  # Backward-rewritten                   : 26
% 0.14/0.38  # Generated clauses                    : 146
% 0.14/0.38  # ...of the previous two non-trivial   : 139
% 0.14/0.38  # Contextual simplify-reflections      : 3
% 0.14/0.38  # Paramodulations                      : 145
% 0.14/0.38  # Factorizations                       : 0
% 0.14/0.38  # Equation resolutions                 : 0
% 0.14/0.38  # Propositional unsat checks           : 0
% 0.14/0.38  #    Propositional check models        : 0
% 0.14/0.38  #    Propositional check unsatisfiable : 0
% 0.14/0.38  #    Propositional clauses             : 0
% 0.14/0.38  #    Propositional clauses after purity: 0
% 0.14/0.38  #    Propositional unsat core size     : 0
% 0.14/0.38  #    Propositional preprocessing time  : 0.000
% 0.14/0.38  #    Propositional encoding time       : 0.000
% 0.14/0.38  #    Propositional solver time         : 0.000
% 0.14/0.38  #    Success case prop preproc time    : 0.000
% 0.14/0.38  #    Success case prop encoding time   : 0.000
% 0.14/0.38  #    Success case prop solver time     : 0.000
% 0.14/0.38  # Current number of processed clauses  : 58
% 0.14/0.38  #    Positive orientable unit clauses  : 12
% 0.14/0.38  #    Positive unorientable unit clauses: 0
% 0.14/0.38  #    Negative unit clauses             : 2
% 0.14/0.38  #    Non-unit-clauses                  : 44
% 0.14/0.38  # Current number of unprocessed clauses: 78
% 0.14/0.38  # ...number of literals in the above   : 391
% 0.14/0.38  # Current number of archived formulas  : 0
% 0.14/0.38  # Current number of archived clauses   : 62
% 0.14/0.38  # Clause-clause subsumption calls (NU) : 692
% 0.14/0.38  # Rec. Clause-clause subsumption calls : 210
% 0.14/0.38  # Non-unit clause-clause subsumptions  : 12
% 0.14/0.38  # Unit Clause-clause subsumption calls : 30
% 0.14/0.38  # Rewrite failures with RHS unbound    : 0
% 0.14/0.38  # BW rewrite match attempts            : 8
% 0.14/0.38  # BW rewrite match successes           : 6
% 0.14/0.38  # Condensation attempts                : 0
% 0.14/0.38  # Condensation successes               : 0
% 0.14/0.38  # Termbank termtop insertions          : 8541
% 0.14/0.38  
% 0.14/0.38  # -------------------------------------------------
% 0.14/0.38  # User time                : 0.034 s
% 0.14/0.38  # System time              : 0.009 s
% 0.14/0.38  # Total time               : 0.042 s
% 0.14/0.38  # Maximum resident set size: 1576 pages
%------------------------------------------------------------------------------
