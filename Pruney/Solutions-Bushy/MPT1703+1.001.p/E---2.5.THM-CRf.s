%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1703+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:36 EST 2020

% Result     : Theorem 0.41s
% Output     : CNFRefutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  100 (2428 expanded)
%              Number of clauses        :   79 ( 991 expanded)
%              Number of leaves         :   10 ( 591 expanded)
%              Depth                    :   19
%              Number of atoms          :  435 (12455 expanded)
%              Number of equality atoms :   63 (1818 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   4 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(t12_tmap_1,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X2 = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
               => ( m1_pre_topc(X2,X1)
                <=> m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tmap_1)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(abstractness_v1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_pre_topc(X1)
       => X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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

fof(t11_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

fof(c_0_10,plain,(
    ! [X21,X22,X23,X24] :
      ( ( X21 = X23
        | g1_pre_topc(X21,X22) != g1_pre_topc(X23,X24)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) )
      & ( X22 = X24
        | g1_pre_topc(X21,X22) != g1_pre_topc(X23,X24)
        | ~ m1_subset_1(X22,k1_zfmisc_1(k1_zfmisc_1(X21))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[free_g1_pre_topc])])])])).

fof(c_0_11,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | m1_subset_1(u1_pre_topc(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v2_pre_topc(X3)
                  & l1_pre_topc(X3) )
               => ( X2 = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                 => ( m1_pre_topc(X2,X1)
                  <=> m1_pre_topc(X3,X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t12_tmap_1])).

cnf(c_0_13,plain,
    ( X1 = X2
    | g1_pre_topc(X1,X3) != g1_pre_topc(X2,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk4_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & esk5_0 = g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))
    & ( ~ m1_pre_topc(esk5_0,esk4_0)
      | ~ m1_pre_topc(esk6_0,esk4_0) )
    & ( m1_pre_topc(esk5_0,esk4_0)
      | m1_pre_topc(esk6_0,esk4_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_12])])])).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ( v1_pre_topc(g1_pre_topc(X15,X16))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) )
      & ( l1_pre_topc(g1_pre_topc(X15,X16))
        | ~ m1_subset_1(X16,k1_zfmisc_1(k1_zfmisc_1(X15))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

cnf(c_0_17,plain,
    ( u1_struct_0(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_13,c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( esk5_0 = g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(X5)
      | ~ v1_pre_topc(X5)
      | X5 = g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[abstractness_v1_pre_topc])])).

cnf(c_0_20,plain,
    ( v1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_21,plain,(
    ! [X7,X8,X9,X11,X13] :
      ( ( r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk1_3(X7,X8,X9),k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk1_3(X7,X8,X9),u1_pre_topc(X7))
        | ~ r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( X9 = k9_subset_1(u1_struct_0(X8),esk1_3(X7,X8,X9),k2_struct_0(X8))
        | ~ r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(X11,u1_pre_topc(X7))
        | X9 != k9_subset_1(u1_struct_0(X8),X11,k2_struct_0(X8))
        | r2_hidden(X9,u1_pre_topc(X8))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X8)))
        | ~ m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk2_2(X7,X8),k1_zfmisc_1(u1_struct_0(X8)))
        | ~ r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(esk2_2(X7,X8),u1_pre_topc(X8))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ r2_hidden(X13,u1_pre_topc(X7))
        | esk2_2(X7,X8) != k9_subset_1(u1_struct_0(X8),X13,k2_struct_0(X8))
        | ~ r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( m1_subset_1(esk3_2(X7,X8),k1_zfmisc_1(u1_struct_0(X7)))
        | r2_hidden(esk2_2(X7,X8),u1_pre_topc(X8))
        | ~ r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( r2_hidden(esk3_2(X7,X8),u1_pre_topc(X7))
        | r2_hidden(esk2_2(X7,X8),u1_pre_topc(X8))
        | ~ r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) )
      & ( esk2_2(X7,X8) = k9_subset_1(u1_struct_0(X8),esk3_2(X7,X8),k2_struct_0(X8))
        | r2_hidden(esk2_2(X7,X8),u1_pre_topc(X8))
        | ~ r1_tarski(k2_struct_0(X8),k2_struct_0(X7))
        | m1_pre_topc(X8,X7)
        | ~ l1_pre_topc(X8)
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_22,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X18)
      | l1_pre_topc(X19) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_23,plain,(
    ! [X6] :
      ( ~ l1_struct_0(X6)
      | k2_struct_0(X6) = u1_struct_0(X6) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_24,plain,(
    ! [X17] :
      ( ~ l1_pre_topc(X17)
      | l1_struct_0(X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_25,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk6_0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != esk5_0
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_26,plain,
    ( X1 = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ l1_pre_topc(X1)
    | ~ v1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_pre_topc(esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk6_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk6_0)))) ),
    inference(spm,[status(thm)],[c_0_20,c_0_18])).

cnf(c_0_28,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_29,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_32,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_33,plain,
    ( X1 = X2
    | g1_pre_topc(X3,X1) != g1_pre_topc(X4,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(X1) = u1_struct_0(esk6_0)
    | X1 != esk5_0
    | ~ v1_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_35,negated_conjecture,
    ( v1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_14]),c_0_28])])).

cnf(c_0_36,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_37,plain,(
    ! [X25,X26] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)))
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_pre_topc(g1_pre_topc(u1_struct_0(X26),u1_pre_topc(X26)),X25)
        | ~ m1_pre_topc(X26,X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tmap_1])])])])).

cnf(c_0_38,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_39,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_40,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,plain,
    ( r2_hidden(X3,u1_pre_topc(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | X3 != k9_subset_1(u1_struct_0(X4),X1,k2_struct_0(X4))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,plain,
    ( u1_pre_topc(X1) = X2
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_33,c_0_14])).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(esk5_0) = u1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])])).

cnf(c_0_44,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( r1_tarski(u1_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_30])).

cnf(c_0_46,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(X1,X2)) = u1_struct_0(esk6_0)
    | g1_pre_topc(X1,X2) != esk5_0
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_20]),c_0_40])).

cnf(c_0_47,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | X1 != k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2))
    | ~ r2_hidden(X3,u1_pre_topc(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X2,X4)
    | ~ l1_pre_topc(X4) ),
    inference(csr,[status(thm)],[c_0_41,c_0_30])).

cnf(c_0_48,negated_conjecture,
    ( u1_pre_topc(X1) = u1_pre_topc(esk6_0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != esk5_0
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_18])).

cnf(c_0_49,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk5_0)) = esk5_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_43]),c_0_35]),c_0_36])])).

cnf(c_0_50,plain,
    ( esk2_2(X1,X2) = k9_subset_1(u1_struct_0(X2),esk3_2(X1,X2),k2_struct_0(X2))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_51,negated_conjecture,
    ( ~ m1_pre_topc(esk5_0,esk4_0)
    | ~ m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_18])).

cnf(c_0_53,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_45,c_0_39])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(esk6_0)
    | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != esk5_0
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_14])).

cnf(c_0_57,plain,
    ( r2_hidden(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X3))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3) ),
    inference(er,[status(thm)],[c_0_47])).

cnf(c_0_58,negated_conjecture,
    ( u1_pre_topc(esk5_0) = u1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_43]),c_0_49]),c_0_36])])).

cnf(c_0_59,plain,
    ( k9_subset_1(u1_struct_0(X1),esk3_2(X2,X1),u1_struct_0(X1)) = esk2_2(X2,X1)
    | r2_hidden(esk2_2(X2,X1),u1_pre_topc(X1))
    | m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),k2_struct_0(X2))
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_50,c_0_39])).

cnf(c_0_60,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk6_0),k2_struct_0(X1))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_43])).

cnf(c_0_61,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0)
    | m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_62,negated_conjecture,
    ( ~ m1_pre_topc(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_63,plain,
    ( m1_subset_1(esk2_2(X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(u1_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_39])).

cnf(c_0_64,plain,
    ( r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk6_0),u1_struct_0(X1))
    | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) != esk5_0
    | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_66,plain,
    ( m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk6_0),X1,k2_struct_0(esk5_0)),u1_pre_topc(esk6_0))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(esk6_0),X1,k2_struct_0(esk5_0)),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ l1_pre_topc(X2) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_43]),c_0_58])).

cnf(c_0_68,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),esk3_2(X1,esk6_0),u1_struct_0(esk6_0)) = esk2_2(X1,esk6_0)
    | r2_hidden(esk2_2(X1,esk6_0),u1_pre_topc(esk6_0))
    | m1_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_28])])).

cnf(c_0_69,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk2_2(X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | m1_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_60]),c_0_28])])).

cnf(c_0_71,plain,
    ( r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_39])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk6_0),u1_struct_0(X1))
    | X2 != esk5_0
    | ~ m1_pre_topc(X2,X1)
    | ~ v1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_26]),c_0_30])).

cnf(c_0_73,plain,
    ( r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(k2_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_39])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k9_subset_1(u1_struct_0(esk6_0),X1,u1_struct_0(esk6_0)),u1_pre_topc(esk6_0))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(esk6_0),X1,u1_struct_0(esk6_0)),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_39]),c_0_43]),c_0_43]),c_0_36])])).

cnf(c_0_75,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),esk3_2(esk4_0,esk6_0),u1_struct_0(esk6_0)) = esk2_2(esk4_0,esk6_0)
    | r2_hidden(esk2_2(esk4_0,esk6_0),u1_pre_topc(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_53])]),c_0_62])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk2_2(esk4_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_69]),c_0_53])]),c_0_62])).

cnf(c_0_77,plain,
    ( r2_hidden(esk3_2(X1,X2),u1_pre_topc(X1))
    | r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_39])).

cnf(c_0_78,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_69]),c_0_35]),c_0_53])])).

cnf(c_0_79,plain,
    ( r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | m1_pre_topc(X2,X1)
    | ~ r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_73,c_0_39])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk6_0),u1_pre_topc(esk6_0))
    | ~ r2_hidden(esk3_2(esk4_0,esk6_0),u1_pre_topc(X1))
    | ~ m1_subset_1(esk3_2(esk4_0,esk6_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk6_0),u1_pre_topc(esk6_0))
    | r2_hidden(esk3_2(esk4_0,esk6_0),u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_28]),c_0_53])]),c_0_62])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk6_0),u1_pre_topc(esk6_0))
    | m1_subset_1(esk3_2(esk4_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_78]),c_0_28]),c_0_53])]),c_0_62])).

cnf(c_0_83,plain,
    ( X1 = k9_subset_1(u1_struct_0(X2),esk1_3(X3,X2,X1),k2_struct_0(X2))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_84,plain,
    ( m1_pre_topc(X2,X1)
    | ~ r2_hidden(esk2_2(X1,X2),u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | esk2_2(X1,X2) != k9_subset_1(u1_struct_0(X2),X3,k2_struct_0(X2))
    | ~ r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_85,negated_conjecture,
    ( r2_hidden(esk2_2(esk4_0,esk6_0),u1_pre_topc(esk6_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_69]),c_0_53])]),c_0_82])).

cnf(c_0_86,plain,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),k2_struct_0(X1)) = X3
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_83,c_0_30])).

cnf(c_0_87,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),X1,k2_struct_0(esk6_0)) != esk2_2(esk4_0,esk6_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(k2_struct_0(esk6_0),k2_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_28]),c_0_53])]),c_0_62])).

cnf(c_0_88,plain,
    ( k9_subset_1(u1_struct_0(X1),esk1_3(X2,X1,X3),u1_struct_0(X1)) = X3
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_39]),c_0_30])).

cnf(c_0_89,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),X1,u1_struct_0(esk6_0)) != esk2_2(esk4_0,esk6_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_39]),c_0_28])])).

cnf(c_0_90,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),esk1_3(X1,esk5_0,X2),u1_struct_0(esk6_0)) = X2
    | ~ r2_hidden(X2,u1_pre_topc(esk6_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_43]),c_0_58])).

cnf(c_0_91,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_92,negated_conjecture,
    ( X1 != esk2_2(esk4_0,esk6_0)
    | ~ r2_hidden(esk1_3(X2,esk5_0,X1),u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk6_0))
    | ~ m1_subset_1(esk1_3(X2,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk4_0))
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),u1_pre_topc(X1))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_91,c_0_30])).

cnf(c_0_94,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_95,negated_conjecture,
    ( X1 != esk2_2(esk4_0,esk6_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk6_0))
    | ~ m1_subset_1(esk1_3(esk4_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_69]),c_0_53]),c_0_58]),c_0_43])])).

cnf(c_0_96,plain,
    ( m1_subset_1(esk1_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_94,c_0_30])).

cnf(c_0_97,negated_conjecture,
    ( X1 != esk2_2(esk4_0,esk6_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_96]),c_0_58]),c_0_43]),c_0_69]),c_0_53])])).

cnf(c_0_98,negated_conjecture,
    ( X1 != esk2_2(esk4_0,esk6_0)
    | ~ r2_hidden(X1,u1_pre_topc(esk6_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_39]),c_0_78]),c_0_53])])).

cnf(c_0_99,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_85]),c_0_76])]),
    [proof]).

%------------------------------------------------------------------------------
