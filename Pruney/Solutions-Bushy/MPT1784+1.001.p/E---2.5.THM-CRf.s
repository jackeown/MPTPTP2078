%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1784+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:44 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 328 expanded)
%              Number of clauses        :   50 ( 133 expanded)
%              Number of leaves         :   15 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :  231 (1097 expanded)
%              Number of equality atoms :   33 (  54 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   40 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t99_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(u1_pre_topc(X1),k5_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_tmap_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t5_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

fof(d8_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k5_tmap_1(X1,X2) = a_2_0_tmap_1(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tmap_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(fraenkel_a_2_0_tmap_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v2_pre_topc(X2)
        & l1_pre_topc(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_tmap_1(X2,X3))
      <=> ? [X4,X5] :
            ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
            & m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
            & X1 = k4_subset_1(u1_struct_0(X2),X4,k9_subset_1(u1_struct_0(X2),X5,X3))
            & r2_hidden(X4,u1_pre_topc(X2))
            & r2_hidden(X5,u1_pre_topc(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_tmap_1)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(dt_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => m1_subset_1(k9_subset_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(redefinition_k4_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X1))
        & m1_subset_1(X3,k1_zfmisc_1(X1)) )
     => k4_subset_1(X1,X2,X3) = k2_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(t1_boole,axiom,(
    ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => r1_tarski(u1_pre_topc(X1),k5_tmap_1(X1,X2)) ) ) ),
    inference(assume_negation,[status(cth)],[t99_tmap_1])).

fof(c_0_16,plain,(
    ! [X43,X44] :
      ( ( ~ m1_subset_1(X43,k1_zfmisc_1(X44))
        | r1_tarski(X43,X44) )
      & ( ~ r1_tarski(X43,X44)
        | m1_subset_1(X43,k1_zfmisc_1(X44)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_17,plain,(
    ! [X16,X17,X18,X19,X20] :
      ( ( ~ r1_tarski(X16,X17)
        | ~ r2_hidden(X18,X16)
        | r2_hidden(X18,X17) )
      & ( r2_hidden(esk1_2(X19,X20),X19)
        | r1_tarski(X19,X20) )
      & ( ~ r2_hidden(esk1_2(X19,X20),X20)
        | r1_tarski(X19,X20) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_18,plain,(
    ! [X48] :
      ( ~ v2_pre_topc(X48)
      | ~ l1_pre_topc(X48)
      | r2_hidden(k1_xboole_0,u1_pre_topc(X48)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_pre_topc])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ~ r1_tarski(u1_pre_topc(esk4_0),k5_tmap_1(esk4_0,esk5_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_22,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k5_tmap_1(X22,X23) = a_2_0_tmap_1(X22,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d8_tmap_1])])])])).

fof(c_0_23,plain,(
    ! [X45,X46,X47] :
      ( ~ r2_hidden(X45,X46)
      | ~ m1_subset_1(X46,k1_zfmisc_1(X47))
      | m1_subset_1(X45,X47) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_24,plain,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | m1_subset_1(u1_pre_topc(X27),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X27)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_30,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( ~ r1_tarski(u1_pre_topc(esk4_0),k5_tmap_1(esk4_0,esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( v2_struct_0(X1)
    | k5_tmap_1(X1,X2) = a_2_0_tmap_1(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(k1_xboole_0,u1_pre_topc(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_36,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_37,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(X38))
      | k9_subset_1(X38,X39,X40) = k3_xboole_0(X39,X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_38,plain,
    ( r1_tarski(X1,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(esk1_2(u1_pre_topc(esk4_0),k5_tmap_1(esk4_0,esk5_0)),u1_pre_topc(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( k5_tmap_1(esk4_0,X1) = a_2_0_tmap_1(esk4_0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_25]),c_0_26])]),c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_42,plain,(
    ! [X28,X29,X30,X33,X34] :
      ( ( m1_subset_1(esk2_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( m1_subset_1(esk3_3(X28,X29,X30),k1_zfmisc_1(u1_struct_0(X29)))
        | ~ r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( X28 = k4_subset_1(u1_struct_0(X29),esk2_3(X28,X29,X30),k9_subset_1(u1_struct_0(X29),esk3_3(X28,X29,X30),X30))
        | ~ r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( r2_hidden(esk2_3(X28,X29,X30),u1_pre_topc(X29))
        | ~ r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( r2_hidden(esk3_3(X28,X29,X30),u1_pre_topc(X29))
        | ~ r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) )
      & ( ~ m1_subset_1(X33,k1_zfmisc_1(u1_struct_0(X29)))
        | ~ m1_subset_1(X34,k1_zfmisc_1(u1_struct_0(X29)))
        | X28 != k4_subset_1(u1_struct_0(X29),X33,k9_subset_1(u1_struct_0(X29),X34,X30))
        | ~ r2_hidden(X33,u1_pre_topc(X29))
        | ~ r2_hidden(X34,u1_pre_topc(X29))
        | r2_hidden(X28,a_2_0_tmap_1(X29,X30))
        | v2_struct_0(X29)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ m1_subset_1(X30,k1_zfmisc_1(u1_struct_0(X29))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_tmap_1])])])])])])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,X1)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_26])).

fof(c_0_45,plain,(
    ! [X42] : k3_xboole_0(X42,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

fof(c_0_46,plain,(
    ! [X24,X25,X26] :
      ( ~ m1_subset_1(X26,k1_zfmisc_1(X24))
      | m1_subset_1(k9_subset_1(X24,X25,X26),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k9_subset_1])])).

cnf(c_0_47,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_48,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_38])).

fof(c_0_49,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X9,X8) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(esk1_2(u1_pre_topc(esk4_0),k5_tmap_1(esk4_0,esk5_0)),X1)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_34,c_0_39])).

cnf(c_0_51,negated_conjecture,
    ( k5_tmap_1(esk4_0,esk5_0) = a_2_0_tmap_1(esk4_0,esk5_0) ),
    inference(spm,[status(thm)],[c_0_40,c_0_41])).

cnf(c_0_52,plain,
    ( r2_hidden(X4,a_2_0_tmap_1(X2,X5))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X4 != k4_subset_1(u1_struct_0(X2),X1,k9_subset_1(u1_struct_0(X2),X3,X5))
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ r2_hidden(X3,u1_pre_topc(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

fof(c_0_53,plain,(
    ! [X13,X14,X15] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(X13))
      | k9_subset_1(X13,X14,X15) = k9_subset_1(X13,X15,X14) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_54,negated_conjecture,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_55,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( m1_subset_1(k9_subset_1(X2,X3,X1),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_57,plain,
    ( k9_subset_1(X1,X2,X1) = k3_xboole_0(X2,X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_58,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_59,plain,(
    ! [X35,X36,X37] :
      ( ~ m1_subset_1(X36,k1_zfmisc_1(X35))
      | ~ m1_subset_1(X37,k1_zfmisc_1(X35))
      | k4_subset_1(X35,X36,X37) = k2_xboole_0(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k4_subset_1])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk1_2(u1_pre_topc(esk4_0),a_2_0_tmap_1(esk4_0,esk5_0)),X1)
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_61,plain,
    ( v2_struct_0(X1)
    | r2_hidden(k4_subset_1(u1_struct_0(X1),X2,k9_subset_1(u1_struct_0(X1),X3,X4)),a_2_0_tmap_1(X1,X4))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X3,u1_pre_topc(X1))
    | ~ r2_hidden(X2,u1_pre_topc(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_62,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),X1,k1_xboole_0) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_54]),c_0_55])).

cnf(c_0_64,plain,
    ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X2)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_48]),c_0_57])).

cnf(c_0_65,plain,
    ( k3_xboole_0(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(spm,[status(thm)],[c_0_55,c_0_58])).

cnf(c_0_66,plain,
    ( k4_subset_1(X2,X1,X3) = k2_xboole_0(X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( m1_subset_1(esk1_2(u1_pre_topc(esk4_0),a_2_0_tmap_1(esk4_0,esk5_0)),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_44])).

fof(c_0_68,plain,(
    ! [X41] : k2_xboole_0(X41,k1_xboole_0) = X41 ),
    inference(variable_rename,[status(thm)],[t1_boole])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(k4_subset_1(u1_struct_0(esk4_0),X1,k9_subset_1(u1_struct_0(esk4_0),X2,X3)),a_2_0_tmap_1(esk4_0,X3))
    | ~ r2_hidden(X2,u1_pre_topc(esk4_0))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_25]),c_0_26])]),c_0_33])).

cnf(c_0_70,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk4_0),k1_xboole_0,X1) = k1_xboole_0 ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_54]),c_0_63])).

cnf(c_0_71,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk4_0),esk1_2(u1_pre_topc(esk4_0),a_2_0_tmap_1(esk4_0,esk5_0)),X1) = k2_xboole_0(esk1_2(u1_pre_topc(esk4_0),a_2_0_tmap_1(esk4_0,esk5_0)),X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_73,plain,
    ( k2_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(k4_subset_1(u1_struct_0(esk4_0),X1,k1_xboole_0),a_2_0_tmap_1(esk4_0,X2))
    | ~ r2_hidden(X1,u1_pre_topc(esk4_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_35]),c_0_70]),c_0_71])])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk1_2(u1_pre_topc(esk4_0),a_2_0_tmap_1(esk4_0,esk5_0)),u1_pre_topc(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_39,c_0_51])).

cnf(c_0_76,negated_conjecture,
    ( k4_subset_1(u1_struct_0(esk4_0),esk1_2(u1_pre_topc(esk4_0),a_2_0_tmap_1(esk4_0,esk5_0)),k1_xboole_0) = esk1_2(u1_pre_topc(esk4_0),a_2_0_tmap_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_54]),c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r2_hidden(esk1_2(u1_pre_topc(esk4_0),a_2_0_tmap_1(esk4_0,esk5_0)),a_2_0_tmap_1(esk4_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_76]),c_0_67])])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk1_2(u1_pre_topc(esk4_0),a_2_0_tmap_1(esk4_0,esk5_0)),a_2_0_tmap_1(esk4_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_41])).

cnf(c_0_79,negated_conjecture,
    ( ~ r1_tarski(u1_pre_topc(esk4_0),a_2_0_tmap_1(esk4_0,esk5_0)) ),
    inference(rw,[status(thm)],[c_0_31,c_0_51])).

cnf(c_0_80,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_78]),c_0_79]),
    [proof]).

%------------------------------------------------------------------------------
