%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:15:57 EST 2020

% Result     : Theorem 0.73s
% Output     : CNFRefutation 0.73s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of clauses        :   23 (  24 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :  214 ( 349 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t94_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
         => r1_tarski(X3,X2) )
     => r1_tarski(k3_tarski(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

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

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(l49_zfmisc_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => r1_tarski(X1,k3_tarski(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(t14_yellow_1,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( r2_hidden(k3_tarski(X1),X1)
       => k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

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

fof(t24_yellow_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(c_0_10,plain,(
    ! [X24,X25] :
      ( ( r2_hidden(esk3_2(X24,X25),X24)
        | r1_tarski(k3_tarski(X24),X25) )
      & ( ~ r1_tarski(esk3_2(X24,X25),X25)
        | r1_tarski(k3_tarski(X24),X25) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).

fof(c_0_11,plain,(
    ! [X31,X32] :
      ( ( ~ m1_subset_1(X31,k1_zfmisc_1(X32))
        | r1_tarski(X31,X32) )
      & ( ~ r1_tarski(X31,X32)
        | m1_subset_1(X31,k1_zfmisc_1(X32)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_12,plain,(
    ! [X33,X34,X35] :
      ( ~ r2_hidden(X33,X34)
      | ~ m1_subset_1(X34,k1_zfmisc_1(X35))
      | m1_subset_1(X33,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_13,plain,(
    ! [X45] :
      ( ~ l1_pre_topc(X45)
      | m1_subset_1(u1_pre_topc(X45),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X45)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_14,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ r1_tarski(esk3_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_18,plain,(
    ! [X18,X19] :
      ( ( r1_tarski(X18,X19)
        | X18 != X19 )
      & ( r1_tarski(X19,X18)
        | X18 != X19 )
      & ( ~ r1_tarski(X18,X19)
        | ~ r1_tarski(X19,X18)
        | X18 = X19 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_19,plain,(
    ! [X22,X23] :
      ( ~ r2_hidden(X22,X23)
      | r1_tarski(X22,k3_tarski(X23)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).

cnf(c_0_20,plain,
    ( r1_tarski(k3_tarski(X1),X2)
    | ~ m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_21,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,k3_tarski(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_24,plain,
    ( r1_tarski(k3_tarski(X1),u1_struct_0(X2))
    | ~ l1_pre_topc(X2)
    | ~ r2_hidden(esk3_2(X1,u1_struct_0(X2)),u1_pre_topc(X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( r2_hidden(esk3_2(X1,X2),X1)
    | r1_tarski(k3_tarski(X1),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_26,plain,(
    ! [X46] :
      ( v1_xboole_0(X46)
      | ~ r2_hidden(k3_tarski(X46),X46)
      | k4_yellow_0(k2_yellow_1(X46)) = k3_tarski(X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).

fof(c_0_27,plain,(
    ! [X5,X6,X7] :
      ( ( ~ v1_xboole_0(X5)
        | ~ r2_hidden(X6,X5) )
      & ( r2_hidden(esk1_1(X7),X7)
        | v1_xboole_0(X7) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_28,plain,
    ( k3_tarski(X1) = X2
    | ~ r1_tarski(k3_tarski(X1),X2)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(X1)),u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

fof(c_0_30,plain,(
    ! [X38,X39,X40,X41] :
      ( ( r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ m1_subset_1(X39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))
        | ~ r1_tarski(X39,u1_pre_topc(X38))
        | r2_hidden(k5_setfam_1(u1_struct_0(X38),X39),u1_pre_topc(X38))
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ r2_hidden(X40,u1_pre_topc(X38))
        | ~ r2_hidden(X41,u1_pre_topc(X38))
        | r2_hidden(k9_subset_1(u1_struct_0(X38),X40,X41),u1_pre_topc(X38))
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_subset_1(esk5_1(X38),k1_zfmisc_1(u1_struct_0(X38)))
        | m1_subset_1(esk4_1(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_subset_1(esk6_1(X38),k1_zfmisc_1(u1_struct_0(X38)))
        | m1_subset_1(esk4_1(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( r2_hidden(esk5_1(X38),u1_pre_topc(X38))
        | m1_subset_1(esk4_1(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( r2_hidden(esk6_1(X38),u1_pre_topc(X38))
        | m1_subset_1(esk4_1(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X38),esk5_1(X38),esk6_1(X38)),u1_pre_topc(X38))
        | m1_subset_1(esk4_1(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_subset_1(esk5_1(X38),k1_zfmisc_1(u1_struct_0(X38)))
        | r1_tarski(esk4_1(X38),u1_pre_topc(X38))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_subset_1(esk6_1(X38),k1_zfmisc_1(u1_struct_0(X38)))
        | r1_tarski(esk4_1(X38),u1_pre_topc(X38))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( r2_hidden(esk5_1(X38),u1_pre_topc(X38))
        | r1_tarski(esk4_1(X38),u1_pre_topc(X38))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( r2_hidden(esk6_1(X38),u1_pre_topc(X38))
        | r1_tarski(esk4_1(X38),u1_pre_topc(X38))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X38),esk5_1(X38),esk6_1(X38)),u1_pre_topc(X38))
        | r1_tarski(esk4_1(X38),u1_pre_topc(X38))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_subset_1(esk5_1(X38),k1_zfmisc_1(u1_struct_0(X38)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X38),esk4_1(X38)),u1_pre_topc(X38))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( m1_subset_1(esk6_1(X38),k1_zfmisc_1(u1_struct_0(X38)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X38),esk4_1(X38)),u1_pre_topc(X38))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( r2_hidden(esk5_1(X38),u1_pre_topc(X38))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X38),esk4_1(X38)),u1_pre_topc(X38))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( r2_hidden(esk6_1(X38),u1_pre_topc(X38))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X38),esk4_1(X38)),u1_pre_topc(X38))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X38),esk5_1(X38),esk6_1(X38)),u1_pre_topc(X38))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X38),esk4_1(X38)),u1_pre_topc(X38))
        | ~ r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))
        | v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_31,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1) ) ),
    inference(assume_negation,[status(cth)],[t24_yellow_1])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X1)
    | k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1)
    | ~ r2_hidden(u1_struct_0(X1),u1_pre_topc(X1)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_35,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,negated_conjecture,
    ( ~ v2_struct_0(esk7_0)
    & v2_pre_topc(esk7_0)
    & l1_pre_topc(esk7_0)
    & k4_yellow_0(k2_yellow_1(u1_pre_topc(esk7_0))) != u1_struct_0(esk7_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).

cnf(c_0_37,plain,
    ( k4_yellow_0(k2_yellow_1(X1)) = k3_tarski(X1)
    | ~ r2_hidden(k3_tarski(X1),X1) ),
    inference(csr,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_38,plain,
    ( k3_tarski(u1_pre_topc(X1)) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_39,negated_conjecture,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(esk7_0))) != u1_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_40,plain,
    ( k4_yellow_0(k2_yellow_1(u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_35])).

cnf(c_0_41,negated_conjecture,
    ( v2_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:29:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.73/0.89  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 0.73/0.89  # and selection function SelectComplexExceptUniqMaxHorn.
% 0.73/0.89  #
% 0.73/0.89  # Preprocessing time       : 0.029 s
% 0.73/0.89  # Presaturation interreduction done
% 0.73/0.89  
% 0.73/0.89  # Proof found!
% 0.73/0.89  # SZS status Theorem
% 0.73/0.89  # SZS output start CNFRefutation
% 0.73/0.89  fof(t94_zfmisc_1, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)=>r1_tarski(X3,X2))=>r1_tarski(k3_tarski(X1),X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 0.73/0.89  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.73/0.89  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.73/0.89  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.73/0.89  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.73/0.89  fof(l49_zfmisc_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>r1_tarski(X1,k3_tarski(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 0.73/0.89  fof(t14_yellow_1, axiom, ![X1]:(~(v1_xboole_0(X1))=>(r2_hidden(k3_tarski(X1),X1)=>k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 0.73/0.89  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.73/0.89  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.73/0.89  fof(t24_yellow_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_yellow_1)).
% 0.73/0.89  fof(c_0_10, plain, ![X24, X25]:((r2_hidden(esk3_2(X24,X25),X24)|r1_tarski(k3_tarski(X24),X25))&(~r1_tarski(esk3_2(X24,X25),X25)|r1_tarski(k3_tarski(X24),X25))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t94_zfmisc_1])])])])).
% 0.73/0.89  fof(c_0_11, plain, ![X31, X32]:((~m1_subset_1(X31,k1_zfmisc_1(X32))|r1_tarski(X31,X32))&(~r1_tarski(X31,X32)|m1_subset_1(X31,k1_zfmisc_1(X32)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.73/0.89  fof(c_0_12, plain, ![X33, X34, X35]:(~r2_hidden(X33,X34)|~m1_subset_1(X34,k1_zfmisc_1(X35))|m1_subset_1(X33,X35)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.73/0.89  fof(c_0_13, plain, ![X45]:(~l1_pre_topc(X45)|m1_subset_1(u1_pre_topc(X45),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X45))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.73/0.89  cnf(c_0_14, plain, (r1_tarski(k3_tarski(X1),X2)|~r1_tarski(esk3_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.73/0.89  cnf(c_0_15, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.73/0.89  cnf(c_0_16, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.73/0.89  cnf(c_0_17, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.73/0.89  fof(c_0_18, plain, ![X18, X19]:(((r1_tarski(X18,X19)|X18!=X19)&(r1_tarski(X19,X18)|X18!=X19))&(~r1_tarski(X18,X19)|~r1_tarski(X19,X18)|X18=X19)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.73/0.89  fof(c_0_19, plain, ![X22, X23]:(~r2_hidden(X22,X23)|r1_tarski(X22,k3_tarski(X23))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l49_zfmisc_1])])).
% 0.73/0.89  cnf(c_0_20, plain, (r1_tarski(k3_tarski(X1),X2)|~m1_subset_1(esk3_2(X1,X2),k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_14, c_0_15])).
% 0.73/0.89  cnf(c_0_21, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)|~r2_hidden(X1,u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.73/0.89  cnf(c_0_22, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.73/0.89  cnf(c_0_23, plain, (r1_tarski(X1,k3_tarski(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.73/0.89  cnf(c_0_24, plain, (r1_tarski(k3_tarski(X1),u1_struct_0(X2))|~l1_pre_topc(X2)|~r2_hidden(esk3_2(X1,u1_struct_0(X2)),u1_pre_topc(X2))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.73/0.89  cnf(c_0_25, plain, (r2_hidden(esk3_2(X1,X2),X1)|r1_tarski(k3_tarski(X1),X2)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.73/0.89  fof(c_0_26, plain, ![X46]:(v1_xboole_0(X46)|(~r2_hidden(k3_tarski(X46),X46)|k4_yellow_0(k2_yellow_1(X46))=k3_tarski(X46))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t14_yellow_1])])])).
% 0.73/0.89  fof(c_0_27, plain, ![X5, X6, X7]:((~v1_xboole_0(X5)|~r2_hidden(X6,X5))&(r2_hidden(esk1_1(X7),X7)|v1_xboole_0(X7))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.73/0.89  cnf(c_0_28, plain, (k3_tarski(X1)=X2|~r1_tarski(k3_tarski(X1),X2)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.73/0.89  cnf(c_0_29, plain, (r1_tarski(k3_tarski(u1_pre_topc(X1)),u1_struct_0(X1))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_24, c_0_25])).
% 0.73/0.89  fof(c_0_30, plain, ![X38, X39, X40, X41]:((((r2_hidden(u1_struct_0(X38),u1_pre_topc(X38))|~v2_pre_topc(X38)|~l1_pre_topc(X38))&(~m1_subset_1(X39,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))|(~r1_tarski(X39,u1_pre_topc(X38))|r2_hidden(k5_setfam_1(u1_struct_0(X38),X39),u1_pre_topc(X38)))|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X38)))|(~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X38)))|(~r2_hidden(X40,u1_pre_topc(X38))|~r2_hidden(X41,u1_pre_topc(X38))|r2_hidden(k9_subset_1(u1_struct_0(X38),X40,X41),u1_pre_topc(X38))))|~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(((m1_subset_1(esk5_1(X38),k1_zfmisc_1(u1_struct_0(X38)))|(m1_subset_1(esk4_1(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38))&((m1_subset_1(esk6_1(X38),k1_zfmisc_1(u1_struct_0(X38)))|(m1_subset_1(esk4_1(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38))&(((r2_hidden(esk5_1(X38),u1_pre_topc(X38))|(m1_subset_1(esk4_1(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38))&(r2_hidden(esk6_1(X38),u1_pre_topc(X38))|(m1_subset_1(esk4_1(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38)))&(~r2_hidden(k9_subset_1(u1_struct_0(X38),esk5_1(X38),esk6_1(X38)),u1_pre_topc(X38))|(m1_subset_1(esk4_1(X38),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X38))))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38)))))&(((m1_subset_1(esk5_1(X38),k1_zfmisc_1(u1_struct_0(X38)))|(r1_tarski(esk4_1(X38),u1_pre_topc(X38))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38))&((m1_subset_1(esk6_1(X38),k1_zfmisc_1(u1_struct_0(X38)))|(r1_tarski(esk4_1(X38),u1_pre_topc(X38))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38))&(((r2_hidden(esk5_1(X38),u1_pre_topc(X38))|(r1_tarski(esk4_1(X38),u1_pre_topc(X38))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38))&(r2_hidden(esk6_1(X38),u1_pre_topc(X38))|(r1_tarski(esk4_1(X38),u1_pre_topc(X38))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38)))&(~r2_hidden(k9_subset_1(u1_struct_0(X38),esk5_1(X38),esk6_1(X38)),u1_pre_topc(X38))|(r1_tarski(esk4_1(X38),u1_pre_topc(X38))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38)))))&((m1_subset_1(esk5_1(X38),k1_zfmisc_1(u1_struct_0(X38)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X38),esk4_1(X38)),u1_pre_topc(X38))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38))&((m1_subset_1(esk6_1(X38),k1_zfmisc_1(u1_struct_0(X38)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X38),esk4_1(X38)),u1_pre_topc(X38))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38))&(((r2_hidden(esk5_1(X38),u1_pre_topc(X38))|(~r2_hidden(k5_setfam_1(u1_struct_0(X38),esk4_1(X38)),u1_pre_topc(X38))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38))&(r2_hidden(esk6_1(X38),u1_pre_topc(X38))|(~r2_hidden(k5_setfam_1(u1_struct_0(X38),esk4_1(X38)),u1_pre_topc(X38))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38)))&(~r2_hidden(k9_subset_1(u1_struct_0(X38),esk5_1(X38),esk6_1(X38)),u1_pre_topc(X38))|(~r2_hidden(k5_setfam_1(u1_struct_0(X38),esk4_1(X38)),u1_pre_topc(X38))|~r2_hidden(u1_struct_0(X38),u1_pre_topc(X38)))|v2_pre_topc(X38)|~l1_pre_topc(X38)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.73/0.89  fof(c_0_31, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1))), inference(assume_negation,[status(cth)],[t24_yellow_1])).
% 0.73/0.89  cnf(c_0_32, plain, (v1_xboole_0(X1)|k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.73/0.89  cnf(c_0_33, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.73/0.89  cnf(c_0_34, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~l1_pre_topc(X1)|~r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.73/0.89  cnf(c_0_35, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.73/0.89  fof(c_0_36, negated_conjecture, (((~v2_struct_0(esk7_0)&v2_pre_topc(esk7_0))&l1_pre_topc(esk7_0))&k4_yellow_0(k2_yellow_1(u1_pre_topc(esk7_0)))!=u1_struct_0(esk7_0)), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_31])])])])).
% 0.73/0.89  cnf(c_0_37, plain, (k4_yellow_0(k2_yellow_1(X1))=k3_tarski(X1)|~r2_hidden(k3_tarski(X1),X1)), inference(csr,[status(thm)],[c_0_32, c_0_33])).
% 0.73/0.89  cnf(c_0_38, plain, (k3_tarski(u1_pre_topc(X1))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_34, c_0_35])).
% 0.73/0.89  cnf(c_0_39, negated_conjecture, (k4_yellow_0(k2_yellow_1(u1_pre_topc(esk7_0)))!=u1_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.73/0.89  cnf(c_0_40, plain, (k4_yellow_0(k2_yellow_1(u1_pre_topc(X1)))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_35])).
% 0.73/0.89  cnf(c_0_41, negated_conjecture, (v2_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.73/0.89  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.73/0.89  cnf(c_0_43, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_41]), c_0_42])]), ['proof']).
% 0.73/0.89  # SZS output end CNFRefutation
% 0.73/0.89  # Proof object total steps             : 44
% 0.73/0.89  # Proof object clause steps            : 23
% 0.73/0.89  # Proof object formula steps           : 21
% 0.73/0.89  # Proof object conjectures             : 7
% 0.73/0.89  # Proof object clause conjectures      : 4
% 0.73/0.89  # Proof object formula conjectures     : 3
% 0.73/0.89  # Proof object initial clauses used    : 13
% 0.73/0.89  # Proof object initial formulas used   : 10
% 0.73/0.89  # Proof object generating inferences   : 9
% 0.73/0.89  # Proof object simplifying inferences  : 5
% 0.73/0.89  # Training examples: 0 positive, 0 negative
% 0.73/0.89  # Parsed axioms                        : 16
% 0.73/0.89  # Removed by relevancy pruning/SinE    : 0
% 0.73/0.89  # Initial clauses                      : 46
% 0.73/0.89  # Removed in clause preprocessing      : 0
% 0.73/0.89  # Initial clauses in saturation        : 46
% 0.73/0.89  # Processed clauses                    : 5416
% 0.73/0.89  # ...of these trivial                  : 71
% 0.73/0.89  # ...subsumed                          : 3960
% 0.73/0.89  # ...remaining for further processing  : 1385
% 0.73/0.89  # Other redundant clauses eliminated   : 5
% 0.73/0.89  # Clauses deleted for lack of memory   : 0
% 0.73/0.89  # Backward-subsumed                    : 17
% 0.73/0.89  # Backward-rewritten                   : 13
% 0.73/0.89  # Generated clauses                    : 41089
% 0.73/0.89  # ...of the previous two non-trivial   : 36616
% 0.73/0.89  # Contextual simplify-reflections      : 6
% 0.73/0.89  # Paramodulations                      : 40990
% 0.73/0.89  # Factorizations                       : 94
% 0.73/0.89  # Equation resolutions                 : 5
% 0.73/0.89  # Propositional unsat checks           : 0
% 0.73/0.89  #    Propositional check models        : 0
% 0.73/0.89  #    Propositional check unsatisfiable : 0
% 0.73/0.89  #    Propositional clauses             : 0
% 0.73/0.89  #    Propositional clauses after purity: 0
% 0.73/0.89  #    Propositional unsat core size     : 0
% 0.73/0.89  #    Propositional preprocessing time  : 0.000
% 0.73/0.89  #    Propositional encoding time       : 0.000
% 0.73/0.89  #    Propositional solver time         : 0.000
% 0.73/0.89  #    Success case prop preproc time    : 0.000
% 0.73/0.89  #    Success case prop encoding time   : 0.000
% 0.73/0.89  #    Success case prop solver time     : 0.000
% 0.73/0.89  # Current number of processed clauses  : 1305
% 0.73/0.89  #    Positive orientable unit clauses  : 41
% 0.73/0.89  #    Positive unorientable unit clauses: 0
% 0.73/0.89  #    Negative unit clauses             : 108
% 0.73/0.89  #    Non-unit-clauses                  : 1156
% 0.73/0.89  # Current number of unprocessed clauses: 31177
% 0.73/0.89  # ...number of literals in the above   : 113277
% 0.73/0.89  # Current number of archived formulas  : 0
% 0.73/0.89  # Current number of archived clauses   : 75
% 0.73/0.89  # Clause-clause subsumption calls (NU) : 256974
% 0.73/0.89  # Rec. Clause-clause subsumption calls : 128406
% 0.73/0.89  # Non-unit clause-clause subsumptions  : 2653
% 0.73/0.89  # Unit Clause-clause subsumption calls : 11645
% 0.73/0.89  # Rewrite failures with RHS unbound    : 0
% 0.73/0.89  # BW rewrite match attempts            : 176
% 0.73/0.89  # BW rewrite match successes           : 3
% 0.73/0.89  # Condensation attempts                : 0
% 0.73/0.89  # Condensation successes               : 0
% 0.73/0.89  # Termbank termtop insertions          : 562372
% 0.73/0.89  
% 0.73/0.89  # -------------------------------------------------
% 0.73/0.89  # User time                : 0.534 s
% 0.73/0.89  # System time              : 0.024 s
% 0.73/0.89  # Total time               : 0.558 s
% 0.73/0.89  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
