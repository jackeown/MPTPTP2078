%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1246+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:58 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 649 expanded)
%              Number of clauses        :   50 ( 218 expanded)
%              Number of leaves         :    9 ( 163 expanded)
%              Depth                    :   12
%              Number of atoms          :  335 (6950 expanded)
%              Number of equality atoms :   24 ( 110 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   38 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t61_tops_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_tops_1(X1,X2))
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( ( v3_pre_topc(X4,X1)
                        & r2_hidden(X3,X4) )
                     => ( ~ r1_xboole_0(X2,X4)
                        & ~ r1_xboole_0(k3_subset_1(u1_struct_0(X1),X2),X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_tops_1)).

fof(t39_tops_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k2_pre_topc(X1,X2))
              <=> ! [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                   => ~ ( v3_pre_topc(X4,X1)
                        & r2_hidden(X3,X4)
                        & r1_xboole_0(X2,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_tops_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(d4_xboole_0,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k3_xboole_0(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( r2_hidden(X4,X1)
            & r2_hidden(X4,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(d2_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k2_tops_1(X1,X2) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(dt_k3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => m1_subset_1(k3_subset_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(c_0_9,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k2_tops_1(X1,X2))
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( ( v3_pre_topc(X4,X1)
                          & r2_hidden(X3,X4) )
                       => ( ~ r1_xboole_0(X2,X4)
                          & ~ r1_xboole_0(k3_subset_1(u1_struct_0(X1),X2),X4) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t61_tops_1])).

fof(c_0_10,negated_conjecture,(
    ! [X37] :
      ( ~ v2_struct_0(esk3_0)
      & v2_pre_topc(esk3_0)
      & l1_pre_topc(esk3_0)
      & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
      & m1_subset_1(esk5_0,u1_struct_0(esk3_0))
      & ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | ~ r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0)) )
      & ( v3_pre_topc(esk6_0,esk3_0)
        | ~ r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0)) )
      & ( r2_hidden(esk5_0,esk6_0)
        | ~ r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0)) )
      & ( r1_xboole_0(esk4_0,esk6_0)
        | r1_xboole_0(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk6_0)
        | ~ r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0)) )
      & ( ~ r1_xboole_0(esk4_0,X37)
        | ~ v3_pre_topc(X37,esk3_0)
        | ~ r2_hidden(esk5_0,X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0)) )
      & ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(esk3_0),esk4_0),X37)
        | ~ v3_pre_topc(X37,esk3_0)
        | ~ r2_hidden(esk5_0,X37)
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(esk3_0)))
        | r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0)) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])])])).

fof(c_0_11,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ r2_hidden(X30,k2_pre_topc(X28,X29))
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X28)))
        | ~ v3_pre_topc(X31,X28)
        | ~ r2_hidden(X30,X31)
        | ~ r1_xboole_0(X29,X31)
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( m1_subset_1(esk2_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X28)))
        | r2_hidden(X30,k2_pre_topc(X28,X29))
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( v3_pre_topc(esk2_3(X28,X29,X30),X28)
        | r2_hidden(X30,k2_pre_topc(X28,X29))
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( r2_hidden(X30,esk2_3(X28,X29,X30))
        | r2_hidden(X30,k2_pre_topc(X28,X29))
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( r1_xboole_0(X29,esk2_3(X28,X29,X30))
        | r2_hidden(X30,k2_pre_topc(X28,X29))
        | ~ m1_subset_1(X30,u1_struct_0(X28))
        | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
        | v2_struct_0(X28)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t39_tops_1])])])])])])).

fof(c_0_12,plain,(
    ! [X25,X26,X27] :
      ( ~ m1_subset_1(X27,k1_zfmisc_1(X25))
      | k9_subset_1(X25,X26,X27) = k3_xboole_0(X26,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_13,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X7))
      | k9_subset_1(X7,X8,X9) = k9_subset_1(X7,X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_14,negated_conjecture,
    ( r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(esk3_0),esk4_0),X1)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_xboole_0(X1,esk2_3(X2,X1,X3))
    | r2_hidden(X3,k2_pre_topc(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | ~ r1_xboole_0(esk4_0,X1)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_17,plain,(
    ! [X12,X13,X14,X15,X16,X17,X18,X19] :
      ( ( r2_hidden(X15,X12)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( r2_hidden(X15,X13)
        | ~ r2_hidden(X15,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(X16,X12)
        | ~ r2_hidden(X16,X13)
        | r2_hidden(X16,X14)
        | X14 != k3_xboole_0(X12,X13) )
      & ( ~ r2_hidden(esk1_3(X17,X18,X19),X19)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X17)
        | ~ r2_hidden(esk1_3(X17,X18,X19),X18)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X17)
        | r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) )
      & ( r2_hidden(esk1_3(X17,X18,X19),X18)
        | r2_hidden(esk1_3(X17,X18,X19),X19)
        | X19 = k3_xboole_0(X17,X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_xboole_0])])])])])])).

fof(c_0_18,plain,(
    ! [X10,X11] :
      ( ~ l1_pre_topc(X10)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
      | k2_tops_1(X10,X11) = k9_subset_1(u1_struct_0(X10),k2_pre_topc(X10,X11),k2_pre_topc(X10,k3_subset_1(u1_struct_0(X10),X11))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tops_1])])])).

cnf(c_0_19,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_21,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

fof(c_0_22,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
      | m1_subset_1(k2_pre_topc(X21,X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_23,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k2_pre_topc(X1,k3_subset_1(u1_struct_0(esk3_0),esk4_0)))
    | r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | ~ v3_pre_topc(esk2_3(X1,k3_subset_1(u1_struct_0(esk3_0),esk4_0),X2),esk3_0)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(esk5_0,esk2_3(X1,k3_subset_1(u1_struct_0(esk3_0),esk4_0),X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk2_3(X1,k3_subset_1(u1_struct_0(esk3_0),esk4_0),X2),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_24,plain,
    ( v3_pre_topc(esk2_3(X1,X2,X3),X1)
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | r2_hidden(X2,k2_pre_topc(X1,esk4_0))
    | ~ v3_pre_topc(esk2_3(X1,esk4_0,X2),esk3_0)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(esk5_0,esk2_3(X1,esk4_0,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(esk2_3(X1,esk4_0,X2),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_15])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_31,plain,
    ( k2_tops_1(X1,X2) = k9_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_32,plain,
    ( k9_subset_1(X1,X2,X3) = k3_xboole_0(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_33,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_34,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X3 != k3_xboole_0(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_36,plain,
    ( r2_hidden(X1,X4)
    | ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | X4 != k3_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(X1,k2_pre_topc(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0)))
    | r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | ~ r2_hidden(esk5_0,esk2_3(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0),X1))
    | ~ m1_subset_1(esk2_3(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0),X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_23,c_0_24]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_38,plain,
    ( r2_hidden(X1,esk2_3(X2,X3,X1))
    | r2_hidden(X1,k2_pre_topc(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | r2_hidden(X1,k2_pre_topc(esk3_0,esk4_0))
    | ~ r2_hidden(esk5_0,esk2_3(esk3_0,esk4_0,X1))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_24]),c_0_25]),c_0_26]),c_0_29])]),c_0_27])).

cnf(c_0_41,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X3,X2)) ),
    inference(er,[status(thm)],[c_0_30])).

cnf(c_0_42,plain,
    ( k3_xboole_0(k2_pre_topc(X1,X2),k2_pre_topc(X1,k3_subset_1(u1_struct_0(X1),X2))) = k2_tops_1(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33]),c_0_34])).

fof(c_0_43,plain,(
    ! [X23,X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(X23))
      | m1_subset_1(k3_subset_1(X23,X24),k1_zfmisc_1(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_subset_1])])).

cnf(c_0_44,plain,
    ( r2_hidden(X1,X2)
    | ~ r2_hidden(X1,k3_xboole_0(X2,X3)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_45,plain,
    ( r2_hidden(X1,k3_xboole_0(X2,X3))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X1,X2) ),
    inference(er,[status(thm)],[c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0)))
    | r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | ~ m1_subset_1(esk2_3(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_47,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X3,k2_pre_topc(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0))
    | r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | ~ m1_subset_1(esk2_3(esk3_0,esk4_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_38]),c_0_39]),c_0_25]),c_0_26]),c_0_29])]),c_0_27])).

cnf(c_0_49,plain,
    ( v2_struct_0(X2)
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X4,X2)
    | ~ r2_hidden(X1,X4)
    | ~ r1_xboole_0(X3,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)))
    | ~ r2_hidden(X1,k2_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_51,plain,
    ( m1_subset_1(k3_subset_1(X2,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ r2_hidden(X1,k2_tops_1(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_44,c_0_42])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,k2_tops_1(X2,X3))
    | ~ r2_hidden(X1,k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),X3)))
    | ~ r2_hidden(X1,k2_pre_topc(X2,X3))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_45,c_0_42])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk5_0,k2_pre_topc(esk3_0,k3_subset_1(u1_struct_0(esk3_0),esk4_0)))
    | r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_25]),c_0_26]),c_0_39])]),c_0_27])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | r2_hidden(esk5_0,k2_pre_topc(esk3_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_47]),c_0_25]),c_0_26]),c_0_29]),c_0_39])]),c_0_27])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | ~ r1_xboole_0(k3_subset_1(u1_struct_0(X1),X2),X3)
    | ~ v3_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X4,k2_tops_1(X1,X2))
    | ~ r2_hidden(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk6_0)
    | r1_xboole_0(k3_subset_1(u1_struct_0(esk3_0),esk4_0),esk6_0)
    | ~ r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_59,negated_conjecture,
    ( v3_pre_topc(esk6_0,esk3_0)
    | ~ r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | ~ r1_xboole_0(X2,X3)
    | ~ v3_pre_topc(X3,X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X4,k2_tops_1(X1,X2))
    | ~ r2_hidden(X4,X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_26]),c_0_29])]),c_0_55])).

cnf(c_0_62,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,k2_tops_1(esk3_0,esk4_0))
    | ~ r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_25]),c_0_26]),c_0_29])]),c_0_27]),c_0_58]),c_0_59])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_64,negated_conjecture,
    ( ~ r1_xboole_0(esk4_0,X1)
    | ~ v3_pre_topc(X1,esk3_0)
    | ~ r2_hidden(esk5_0,X1)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_25]),c_0_26]),c_0_29]),c_0_39])]),c_0_27])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(esk4_0,esk6_0)
    | ~ r2_hidden(esk5_0,k2_tops_1(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_39])])).

cnf(c_0_66,negated_conjecture,
    ( ~ v3_pre_topc(esk6_0,esk3_0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_58]),c_0_63]),c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(esk3_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_59]),c_0_61])).

cnf(c_0_68,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_51]),c_0_29])]),
    [proof]).

%------------------------------------------------------------------------------
