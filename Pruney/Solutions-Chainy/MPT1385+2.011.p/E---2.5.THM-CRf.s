%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:32 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 497 expanded)
%              Number of clauses        :   78 ( 211 expanded)
%              Number of leaves         :   16 ( 121 expanded)
%              Depth                    :   19
%              Number of atoms          :  419 (2357 expanded)
%              Number of equality atoms :   62 ( 354 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_subset_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t10_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))
              <=> m1_connsp_2(X3,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_connsp_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d2_connsp_2,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m2_connsp_2(X3,X1,X2)
              <=> r1_tarski(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(dt_m2_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ! [X3] :
          ( m2_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(d1_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( m1_connsp_2(X3,X1,X2)
              <=> r2_hidden(X2,k1_tops_1(X1,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_connsp_2)).

fof(dt_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ! [X3] :
          ( m1_connsp_2(X3,X1,X2)
         => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_16,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,X16)
      | m1_subset_1(k1_tarski(X15),k1_zfmisc_1(X16)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).

fof(c_0_17,plain,(
    ! [X14] : k2_tarski(X14,X14) = k1_tarski(X14) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_18,plain,(
    ! [X24,X25,X26] :
      ( ~ r2_hidden(X24,X25)
      | ~ m1_subset_1(X25,k1_zfmisc_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_19,plain,
    ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_21,plain,(
    ! [X5,X6,X7,X8,X9,X10,X11,X12] :
      ( ( ~ r2_hidden(X8,X7)
        | X8 = X5
        | X8 = X6
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X5
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( X9 != X6
        | r2_hidden(X9,X7)
        | X7 != k2_tarski(X5,X6) )
      & ( esk1_3(X10,X11,X12) != X10
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( esk1_3(X10,X11,X12) != X11
        | ~ r2_hidden(esk1_3(X10,X11,X12),X12)
        | X12 = k2_tarski(X10,X11) )
      & ( r2_hidden(esk1_3(X10,X11,X12),X12)
        | esk1_3(X10,X11,X12) = X10
        | esk1_3(X10,X11,X12) = X11
        | X12 = k2_tarski(X10,X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_24,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_25,plain,(
    ! [X21,X22,X23] :
      ( ~ r2_hidden(X21,X22)
      | ~ m1_subset_1(X22,k1_zfmisc_1(X23))
      | m1_subset_1(X21,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_26,plain,(
    ! [X17,X18] :
      ( ~ m1_subset_1(X17,X18)
      | v1_xboole_0(X18)
      | r2_hidden(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_27,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,k2_tarski(X3,X3))
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_29,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).

cnf(c_0_30,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_31,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk1_3(X1,X2,X3) != X1
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r2_hidden(esk1_3(X1,X2,X3),X3)
    | esk1_3(X1,X2,X3) = X1
    | esk1_3(X1,X2,X3) = X2
    | X3 = k2_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_36,plain,(
    ! [X31,X32] :
      ( v1_xboole_0(X31)
      | ~ m1_subset_1(X32,X31)
      | k6_domain_1(X31,X32) = k1_tarski(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_37,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,k2_tarski(X3,X3))
    | ~ r2_hidden(X3,X2) ),
    inference(spm,[status(thm)],[c_0_30,c_0_23])).

cnf(c_0_38,plain,
    ( X1 = k2_tarski(X2,X3)
    | v1_xboole_0(X1)
    | esk1_3(X2,X3,X1) != X2
    | ~ m1_subset_1(esk1_3(X2,X3,X1),X1) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X1
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X3
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X4
    | k2_tarski(X3,X4) = k2_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_29])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_37,c_0_29])).

cnf(c_0_43,plain,
    ( esk1_3(X1,X2,k2_tarski(X3,X4)) = X4
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X3
    | esk1_3(X1,X2,k2_tarski(X3,X4)) = X2
    | k2_tarski(X3,X4) = k2_tarski(X1,X2)
    | ~ m1_subset_1(X1,k2_tarski(X3,X4)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_39]),c_0_40])).

cnf(c_0_44,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_41,c_0_20])).

cnf(c_0_45,plain,
    ( m1_subset_1(X1,k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_29])).

fof(c_0_46,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))
                <=> m1_connsp_2(X3,X1,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t10_connsp_2])).

fof(c_0_47,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_48,plain,(
    ! [X36,X37,X38] :
      ( ( ~ m2_connsp_2(X38,X36,X37)
        | r1_tarski(X37,k1_tops_1(X36,X38))
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ r1_tarski(X37,k1_tops_1(X36,X38))
        | m2_connsp_2(X38,X36,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).

fof(c_0_49,plain,(
    ! [X42,X43,X44] :
      ( ~ v2_pre_topc(X42)
      | ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
      | ~ m2_connsp_2(X44,X42,X43)
      | m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).

cnf(c_0_50,plain,
    ( esk1_3(X1,X2,k6_domain_1(X3,X4)) = X2
    | esk1_3(X1,X2,k6_domain_1(X3,X4)) = X4
    | k6_domain_1(X3,X4) = k2_tarski(X1,X2)
    | v1_xboole_0(X3)
    | ~ m1_subset_1(X1,k6_domain_1(X3,X4))
    | ~ m1_subset_1(X4,X3) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_51,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(X2,k6_domain_1(X1,X2))
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_44])).

fof(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))
    & ( ~ m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
      | ~ m1_connsp_2(esk4_0,esk2_0,esk3_0) )
    & ( m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
      | m1_connsp_2(esk4_0,esk2_0,esk3_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_46])])])])).

cnf(c_0_53,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_54,plain,
    ( r1_tarski(X3,k1_tops_1(X2,X1))
    | ~ m2_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m2_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,plain,
    ( esk1_3(X1,X2,k6_domain_1(X3,X1)) = X1
    | esk1_3(X1,X2,k6_domain_1(X3,X1)) = X2
    | k6_domain_1(X3,X1) = k2_tarski(X1,X2)
    | v1_xboole_0(X3)
    | ~ m1_subset_1(X1,X3) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,plain,
    ( m1_subset_1(X1,X2)
    | ~ r1_tarski(X3,X2)
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_30,c_0_53])).

cnf(c_0_59,plain,
    ( r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m2_connsp_2(X3,X2,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_60,plain,(
    ! [X29,X30] :
      ( v1_xboole_0(X29)
      | ~ m1_subset_1(X30,X29)
      | m1_subset_1(k6_domain_1(X29,X30),k1_zfmisc_1(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_61,negated_conjecture,
    ( esk1_3(esk3_0,X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) = esk3_0
    | esk1_3(esk3_0,X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) = X1
    | k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k2_tarski(esk3_0,X1)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,k1_tops_1(X2,X3))
    | ~ m2_connsp_2(X3,X2,X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_63,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_53])).

cnf(c_0_64,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_65,plain,
    ( X3 = k2_tarski(X1,X2)
    | esk1_3(X1,X2,X3) != X2
    | ~ r2_hidden(esk1_3(X1,X2,X3),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_66,negated_conjecture,
    ( esk1_3(esk3_0,esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) = esk3_0
    | k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k2_tarski(esk3_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_61])])).

fof(c_0_67,plain,(
    ! [X33,X34,X35] :
      ( ( ~ m1_connsp_2(X35,X33,X34)
        | r2_hidden(X34,k1_tops_1(X33,X35))
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ r2_hidden(X34,k1_tops_1(X33,X35))
        | m1_connsp_2(X35,X33,X34)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v2_pre_topc(X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

cnf(c_0_68,plain,
    ( m1_subset_1(X1,k1_tops_1(X2,X3))
    | ~ m2_connsp_2(X3,X2,X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X4,u1_struct_0(X2))
    | ~ r2_hidden(X1,X4) ),
    inference(spm,[status(thm)],[c_0_62,c_0_53])).

cnf(c_0_69,negated_conjecture,
    ( m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
    | m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_70,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_71,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_72,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_73,plain,
    ( ~ m2_connsp_2(X1,X2,X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_xboole_0(k1_tops_1(X2,X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X4,X3) ),
    inference(spm,[status(thm)],[c_0_63,c_0_59])).

cnf(c_0_74,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k2_tarski(X2,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_64,c_0_44])).

cnf(c_0_75,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k2_tarski(esk3_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_76,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(X2,k6_domain_1(X1,X2))
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_44])).

cnf(c_0_77,plain,
    ( m1_connsp_2(X3,X2,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | m1_subset_1(X1,k1_tops_1(esk2_0,esk4_0))
    | ~ r1_tarski(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_70]),c_0_71])])).

cnf(c_0_79,plain,
    ( r1_tarski(k6_domain_1(X1,X2),X1)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_72,c_0_64])).

cnf(c_0_80,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ m2_connsp_2(X2,X1,k2_tarski(X3,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v1_xboole_0(k1_tops_1(X1,X2))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ r2_hidden(X4,k2_tarski(X3,X3)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_81,negated_conjecture,
    ( m2_connsp_2(esk4_0,esk2_0,k2_tarski(esk3_0,esk3_0))
    | m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_44]),c_0_57])])).

cnf(c_0_82,plain,
    ( m2_connsp_2(X3,X2,X1)
    | ~ r1_tarski(X1,k1_tops_1(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_83,plain,
    ( r1_tarski(k2_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X2) ),
    inference(spm,[status(thm)],[c_0_72,c_0_23])).

cnf(c_0_84,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk2_0),esk3_0) = k2_tarski(esk3_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_57])])).

cnf(c_0_85,plain,
    ( m1_connsp_2(X1,X2,X3)
    | v2_struct_0(X2)
    | v1_xboole_0(k1_tops_1(X2,X1))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_tops_1(X2,X1))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(spm,[status(thm)],[c_0_77,c_0_32])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_87,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_88,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(X1,k1_tops_1(esk2_0,esk4_0))
    | ~ r2_hidden(X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_57])])).

cnf(c_0_89,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v1_xboole_0(k1_tops_1(esk2_0,esk4_0))
    | ~ r2_hidden(X1,k2_tarski(esk3_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_81]),c_0_70]),c_0_71]),c_0_57])])).

cnf(c_0_90,negated_conjecture,
    ( ~ m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))
    | ~ m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_91,plain,
    ( m2_connsp_2(X1,X2,k2_tarski(X3,X3))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(k2_tarski(X3,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X3,k1_tops_1(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(k2_tarski(esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_84]),c_0_57])])).

cnf(c_0_93,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,X1)
    | v1_xboole_0(k1_tops_1(esk2_0,esk4_0))
    | ~ m1_subset_1(X1,k1_tops_1(esk2_0,esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_70]),c_0_71])]),c_0_87])).

cnf(c_0_94,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_76]),c_0_57])])).

cnf(c_0_95,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ v1_xboole_0(k1_tops_1(esk2_0,esk4_0)) ),
    inference(spm,[status(thm)],[c_0_89,c_0_29])).

fof(c_0_96,plain,(
    ! [X39,X40,X41] :
      ( v2_struct_0(X39)
      | ~ v2_pre_topc(X39)
      | ~ l1_pre_topc(X39)
      | ~ m1_subset_1(X40,u1_struct_0(X39))
      | ~ m1_connsp_2(X41,X39,X40)
      | m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

cnf(c_0_97,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m2_connsp_2(esk4_0,esk2_0,k2_tarski(esk3_0,esk3_0))
    | ~ m1_connsp_2(esk4_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_44]),c_0_57])])).

cnf(c_0_98,negated_conjecture,
    ( m2_connsp_2(X1,esk2_0,k2_tarski(esk3_0,esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,X1)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_70]),c_0_71])])).

cnf(c_0_99,negated_conjecture,
    ( m1_connsp_2(esk4_0,esk2_0,esk3_0)
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_94]),c_0_57])]),c_0_95])).

cnf(c_0_100,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_101,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_96])).

fof(c_0_102,plain,(
    ! [X28] :
      ( v2_struct_0(X28)
      | ~ l1_struct_0(X28)
      | ~ v1_xboole_0(u1_struct_0(X28)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_103,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_98]),c_0_86])]),c_0_99])).

cnf(c_0_104,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[c_0_100,c_0_101])).

cnf(c_0_105,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_106,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_104]),c_0_70]),c_0_71]),c_0_57])]),c_0_87]),c_0_99])).

fof(c_0_107,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | l1_struct_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_108,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_106]),c_0_87])).

cnf(c_0_109,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_107])).

cnf(c_0_110,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108,c_0_109]),c_0_71])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:20:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___207_C01_F1_SE_CS_SP_PI_S5PRR_S0Y
% 0.19/0.41  # and selection function SelectMaxLComplexAvoidPosPred.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.040 s
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t63_subset_1, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 0.19/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.41  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.41  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.41  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.19/0.41  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.41  fof(t10_connsp_2, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))<=>m1_connsp_2(X3,X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_connsp_2)).
% 0.19/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.19/0.41  fof(d2_connsp_2, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,X2)<=>r1_tarski(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_connsp_2)).
% 0.19/0.41  fof(dt_m2_connsp_2, axiom, ![X1, X2]:(((v2_pre_topc(X1)&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>![X3]:(m2_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m2_connsp_2)).
% 0.19/0.41  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.19/0.41  fof(d1_connsp_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m1_connsp_2(X3,X1,X2)<=>r2_hidden(X2,k1_tops_1(X1,X3)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_connsp_2)).
% 0.19/0.41  fof(dt_m1_connsp_2, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,u1_struct_0(X1)))=>![X3]:(m1_connsp_2(X3,X1,X2)=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 0.19/0.41  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.19/0.41  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.41  fof(c_0_16, plain, ![X15, X16]:(~r2_hidden(X15,X16)|m1_subset_1(k1_tarski(X15),k1_zfmisc_1(X16))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_subset_1])])).
% 0.19/0.41  fof(c_0_17, plain, ![X14]:k2_tarski(X14,X14)=k1_tarski(X14), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  fof(c_0_18, plain, ![X24, X25, X26]:(~r2_hidden(X24,X25)|~m1_subset_1(X25,k1_zfmisc_1(X26))|~v1_xboole_0(X26)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.41  cnf(c_0_19, plain, (m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_20, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.41  fof(c_0_21, plain, ![X5, X6, X7, X8, X9, X10, X11, X12]:(((~r2_hidden(X8,X7)|(X8=X5|X8=X6)|X7!=k2_tarski(X5,X6))&((X9!=X5|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))&(X9!=X6|r2_hidden(X9,X7)|X7!=k2_tarski(X5,X6))))&(((esk1_3(X10,X11,X12)!=X10|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11))&(esk1_3(X10,X11,X12)!=X11|~r2_hidden(esk1_3(X10,X11,X12),X12)|X12=k2_tarski(X10,X11)))&(r2_hidden(esk1_3(X10,X11,X12),X12)|(esk1_3(X10,X11,X12)=X10|esk1_3(X10,X11,X12)=X11)|X12=k2_tarski(X10,X11)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_22, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.41  cnf(c_0_23, plain, (m1_subset_1(k2_tarski(X1,X1),k1_zfmisc_1(X2))|~r2_hidden(X1,X2)), inference(rw,[status(thm)],[c_0_19, c_0_20])).
% 0.19/0.41  cnf(c_0_24, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  fof(c_0_25, plain, ![X21, X22, X23]:(~r2_hidden(X21,X22)|~m1_subset_1(X22,k1_zfmisc_1(X23))|m1_subset_1(X21,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.41  fof(c_0_26, plain, ![X17, X18]:(~m1_subset_1(X17,X18)|(v1_xboole_0(X18)|r2_hidden(X17,X18))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.19/0.41  cnf(c_0_27, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_28, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,k2_tarski(X3,X3))|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.19/0.41  cnf(c_0_29, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_24])])).
% 0.19/0.41  cnf(c_0_30, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_31, plain, (X3=k2_tarski(X1,X2)|esk1_3(X1,X2,X3)!=X1|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_32, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.19/0.41  cnf(c_0_33, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_27])).
% 0.19/0.41  cnf(c_0_34, plain, (r2_hidden(esk1_3(X1,X2,X3),X3)|esk1_3(X1,X2,X3)=X1|esk1_3(X1,X2,X3)=X2|X3=k2_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_35, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.19/0.41  fof(c_0_36, plain, ![X31, X32]:(v1_xboole_0(X31)|~m1_subset_1(X32,X31)|k6_domain_1(X31,X32)=k1_tarski(X32)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.41  cnf(c_0_37, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,k2_tarski(X3,X3))|~r2_hidden(X3,X2)), inference(spm,[status(thm)],[c_0_30, c_0_23])).
% 0.19/0.41  cnf(c_0_38, plain, (X1=k2_tarski(X2,X3)|v1_xboole_0(X1)|esk1_3(X2,X3,X1)!=X2|~m1_subset_1(esk1_3(X2,X3,X1),X1)), inference(spm,[status(thm)],[c_0_31, c_0_32])).
% 0.19/0.41  cnf(c_0_39, plain, (esk1_3(X1,X2,k2_tarski(X3,X4))=X2|esk1_3(X1,X2,k2_tarski(X3,X4))=X1|esk1_3(X1,X2,k2_tarski(X3,X4))=X3|esk1_3(X1,X2,k2_tarski(X3,X4))=X4|k2_tarski(X3,X4)=k2_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_33, c_0_34])).
% 0.19/0.41  cnf(c_0_40, plain, (~v1_xboole_0(k2_tarski(X1,X2))), inference(spm,[status(thm)],[c_0_35, c_0_29])).
% 0.19/0.41  cnf(c_0_41, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.41  cnf(c_0_42, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_37, c_0_29])).
% 0.19/0.41  cnf(c_0_43, plain, (esk1_3(X1,X2,k2_tarski(X3,X4))=X4|esk1_3(X1,X2,k2_tarski(X3,X4))=X3|esk1_3(X1,X2,k2_tarski(X3,X4))=X2|k2_tarski(X3,X4)=k2_tarski(X1,X2)|~m1_subset_1(X1,k2_tarski(X3,X4))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_39]), c_0_40])).
% 0.19/0.41  cnf(c_0_44, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_41, c_0_20])).
% 0.19/0.41  cnf(c_0_45, plain, (m1_subset_1(X1,k2_tarski(X2,X1))), inference(spm,[status(thm)],[c_0_42, c_0_29])).
% 0.19/0.41  fof(c_0_46, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(m2_connsp_2(X3,X1,k6_domain_1(u1_struct_0(X1),X2))<=>m1_connsp_2(X3,X1,X2)))))), inference(assume_negation,[status(cth)],[t10_connsp_2])).
% 0.19/0.41  fof(c_0_47, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.19/0.41  fof(c_0_48, plain, ![X36, X37, X38]:((~m2_connsp_2(X38,X36,X37)|r1_tarski(X37,k1_tops_1(X36,X38))|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(~r1_tarski(X37,k1_tops_1(X36,X38))|m2_connsp_2(X38,X36,X37)|~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))|~m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_connsp_2])])])])).
% 0.19/0.41  fof(c_0_49, plain, ![X42, X43, X44]:(~v2_pre_topc(X42)|~l1_pre_topc(X42)|~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))|(~m2_connsp_2(X44,X42,X43)|m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X42))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m2_connsp_2])])])).
% 0.19/0.41  cnf(c_0_50, plain, (esk1_3(X1,X2,k6_domain_1(X3,X4))=X2|esk1_3(X1,X2,k6_domain_1(X3,X4))=X4|k6_domain_1(X3,X4)=k2_tarski(X1,X2)|v1_xboole_0(X3)|~m1_subset_1(X1,k6_domain_1(X3,X4))|~m1_subset_1(X4,X3)), inference(spm,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.41  cnf(c_0_51, plain, (v1_xboole_0(X1)|m1_subset_1(X2,k6_domain_1(X1,X2))|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_45, c_0_44])).
% 0.19/0.41  fof(c_0_52, negated_conjecture, (((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&(m1_subset_1(esk3_0,u1_struct_0(esk2_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))&((~m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|~m1_connsp_2(esk4_0,esk2_0,esk3_0))&(m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|m1_connsp_2(esk4_0,esk2_0,esk3_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_46])])])])).
% 0.19/0.41  cnf(c_0_53, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.41  cnf(c_0_54, plain, (r1_tarski(X3,k1_tops_1(X2,X1))|~m2_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_55, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m2_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.19/0.41  cnf(c_0_56, plain, (esk1_3(X1,X2,k6_domain_1(X3,X1))=X1|esk1_3(X1,X2,k6_domain_1(X3,X1))=X2|k6_domain_1(X3,X1)=k2_tarski(X1,X2)|v1_xboole_0(X3)|~m1_subset_1(X1,X3)), inference(spm,[status(thm)],[c_0_50, c_0_51])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (m1_subset_1(esk3_0,u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_58, plain, (m1_subset_1(X1,X2)|~r1_tarski(X3,X2)|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_30, c_0_53])).
% 0.19/0.41  cnf(c_0_59, plain, (r1_tarski(X1,k1_tops_1(X2,X3))|~m2_connsp_2(X3,X2,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[c_0_54, c_0_55])).
% 0.19/0.41  fof(c_0_60, plain, ![X29, X30]:(v1_xboole_0(X29)|~m1_subset_1(X30,X29)|m1_subset_1(k6_domain_1(X29,X30),k1_zfmisc_1(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.19/0.41  cnf(c_0_61, negated_conjecture, (esk1_3(esk3_0,X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0))=esk3_0|esk1_3(esk3_0,X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0))=X1|k6_domain_1(u1_struct_0(esk2_0),esk3_0)=k2_tarski(esk3_0,X1)|v1_xboole_0(u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.41  cnf(c_0_62, plain, (m1_subset_1(X1,k1_tops_1(X2,X3))|~m2_connsp_2(X3,X2,X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.41  cnf(c_0_63, plain, (~r1_tarski(X1,X2)|~v1_xboole_0(X2)|~r2_hidden(X3,X1)), inference(spm,[status(thm)],[c_0_22, c_0_53])).
% 0.19/0.41  cnf(c_0_64, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_60])).
% 0.19/0.41  cnf(c_0_65, plain, (X3=k2_tarski(X1,X2)|esk1_3(X1,X2,X3)!=X2|~r2_hidden(esk1_3(X1,X2,X3),X3)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (esk1_3(esk3_0,esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))=esk3_0|k6_domain_1(u1_struct_0(esk2_0),esk3_0)=k2_tarski(esk3_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(er,[status(thm)],[inference(ef,[status(thm)],[c_0_61])])).
% 0.19/0.41  fof(c_0_67, plain, ![X33, X34, X35]:((~m1_connsp_2(X35,X33,X34)|r2_hidden(X34,k1_tops_1(X33,X35))|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))&(~r2_hidden(X34,k1_tops_1(X33,X35))|m1_connsp_2(X35,X33,X34)|~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v2_pre_topc(X33)|~l1_pre_topc(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).
% 0.19/0.41  cnf(c_0_68, plain, (m1_subset_1(X1,k1_tops_1(X2,X3))|~m2_connsp_2(X3,X2,X4)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~r1_tarski(X4,u1_struct_0(X2))|~r2_hidden(X1,X4)), inference(spm,[status(thm)],[c_0_62, c_0_53])).
% 0.19/0.41  cnf(c_0_69, negated_conjecture, (m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_70, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_71, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_72, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.41  cnf(c_0_73, plain, (~m2_connsp_2(X1,X2,X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_xboole_0(k1_tops_1(X2,X1))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X4,X3)), inference(spm,[status(thm)],[c_0_63, c_0_59])).
% 0.19/0.41  cnf(c_0_74, plain, (v1_xboole_0(X1)|m1_subset_1(k2_tarski(X2,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_64, c_0_44])).
% 0.19/0.41  cnf(c_0_75, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk3_0)=k2_tarski(esk3_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(esk3_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 0.19/0.41  cnf(c_0_76, plain, (v1_xboole_0(X1)|r2_hidden(X2,k6_domain_1(X1,X2))|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_29, c_0_44])).
% 0.19/0.41  cnf(c_0_77, plain, (m1_connsp_2(X3,X2,X1)|v2_struct_0(X2)|~r2_hidden(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.41  cnf(c_0_78, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,esk3_0)|m1_subset_1(X1,k1_tops_1(esk2_0,esk4_0))|~r1_tarski(k6_domain_1(u1_struct_0(esk2_0),esk3_0),u1_struct_0(esk2_0))|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68, c_0_69]), c_0_70]), c_0_71])])).
% 0.19/0.41  cnf(c_0_79, plain, (r1_tarski(k6_domain_1(X1,X2),X1)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(spm,[status(thm)],[c_0_72, c_0_64])).
% 0.19/0.41  cnf(c_0_80, plain, (v1_xboole_0(u1_struct_0(X1))|~m2_connsp_2(X2,X1,k2_tarski(X3,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v1_xboole_0(k1_tops_1(X1,X2))|~m1_subset_1(X3,u1_struct_0(X1))|~r2_hidden(X4,k2_tarski(X3,X3))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.19/0.41  cnf(c_0_81, negated_conjecture, (m2_connsp_2(esk4_0,esk2_0,k2_tarski(esk3_0,esk3_0))|m1_connsp_2(esk4_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_44]), c_0_57])])).
% 0.19/0.41  cnf(c_0_82, plain, (m2_connsp_2(X3,X2,X1)|~r1_tarski(X1,k1_tops_1(X2,X3))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_83, plain, (r1_tarski(k2_tarski(X1,X1),X2)|~r2_hidden(X1,X2)), inference(spm,[status(thm)],[c_0_72, c_0_23])).
% 0.19/0.41  cnf(c_0_84, negated_conjecture, (k6_domain_1(u1_struct_0(esk2_0),esk3_0)=k2_tarski(esk3_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_57])])).
% 0.19/0.41  cnf(c_0_85, plain, (m1_connsp_2(X1,X2,X3)|v2_struct_0(X2)|v1_xboole_0(k1_tops_1(X2,X1))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,k1_tops_1(X2,X1))|~m1_subset_1(X3,u1_struct_0(X2))), inference(spm,[status(thm)],[c_0_77, c_0_32])).
% 0.19/0.41  cnf(c_0_86, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_87, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_88, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))|m1_subset_1(X1,k1_tops_1(esk2_0,esk4_0))|~r2_hidden(X1,k6_domain_1(u1_struct_0(esk2_0),esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_57])])).
% 0.19/0.41  cnf(c_0_89, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))|~v1_xboole_0(k1_tops_1(esk2_0,esk4_0))|~r2_hidden(X1,k2_tarski(esk3_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_81]), c_0_70]), c_0_71]), c_0_57])])).
% 0.19/0.41  cnf(c_0_90, negated_conjecture, (~m2_connsp_2(esk4_0,esk2_0,k6_domain_1(u1_struct_0(esk2_0),esk3_0))|~m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.19/0.41  cnf(c_0_91, plain, (m2_connsp_2(X1,X2,k2_tarski(X3,X3))|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(k2_tarski(X3,X3),k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X3,k1_tops_1(X2,X1))), inference(spm,[status(thm)],[c_0_82, c_0_83])).
% 0.19/0.41  cnf(c_0_92, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|m1_subset_1(k2_tarski(esk3_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk2_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_84]), c_0_57])])).
% 0.19/0.41  cnf(c_0_93, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,X1)|v1_xboole_0(k1_tops_1(esk2_0,esk4_0))|~m1_subset_1(X1,k1_tops_1(esk2_0,esk4_0))|~m1_subset_1(X1,u1_struct_0(esk2_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_70]), c_0_71])]), c_0_87])).
% 0.19/0.41  cnf(c_0_94, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))|m1_subset_1(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_76]), c_0_57])])).
% 0.19/0.41  cnf(c_0_95, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))|~v1_xboole_0(k1_tops_1(esk2_0,esk4_0))), inference(spm,[status(thm)],[c_0_89, c_0_29])).
% 0.19/0.41  fof(c_0_96, plain, ![X39, X40, X41]:(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|~m1_subset_1(X40,u1_struct_0(X39))|(~m1_connsp_2(X41,X39,X40)|m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X39))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).
% 0.19/0.41  cnf(c_0_97, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~m2_connsp_2(esk4_0,esk2_0,k2_tarski(esk3_0,esk3_0))|~m1_connsp_2(esk4_0,esk2_0,esk3_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_44]), c_0_57])])).
% 0.19/0.41  cnf(c_0_98, negated_conjecture, (m2_connsp_2(X1,esk2_0,k2_tarski(esk3_0,esk3_0))|v1_xboole_0(u1_struct_0(esk2_0))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk2_0)))|~r2_hidden(esk3_0,k1_tops_1(esk2_0,X1))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_70]), c_0_71])])).
% 0.19/0.41  cnf(c_0_99, negated_conjecture, (m1_connsp_2(esk4_0,esk2_0,esk3_0)|v1_xboole_0(u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_94]), c_0_57])]), c_0_95])).
% 0.19/0.41  cnf(c_0_100, plain, (r2_hidden(X3,k1_tops_1(X2,X1))|v2_struct_0(X2)|~m1_connsp_2(X1,X2,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_subset_1(X3,u1_struct_0(X2))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_67])).
% 0.19/0.41  cnf(c_0_101, plain, (v2_struct_0(X1)|m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_connsp_2(X3,X1,X2)), inference(split_conjunct,[status(thm)],[c_0_96])).
% 0.19/0.41  fof(c_0_102, plain, ![X28]:(v2_struct_0(X28)|~l1_struct_0(X28)|~v1_xboole_0(u1_struct_0(X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.19/0.41  cnf(c_0_103, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))|~r2_hidden(esk3_0,k1_tops_1(esk2_0,esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_98]), c_0_86])]), c_0_99])).
% 0.19/0.41  cnf(c_0_104, plain, (v2_struct_0(X1)|r2_hidden(X2,k1_tops_1(X1,X3))|~m1_connsp_2(X3,X1,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[c_0_100, c_0_101])).
% 0.19/0.41  cnf(c_0_105, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_102])).
% 0.19/0.41  cnf(c_0_106, negated_conjecture, (v1_xboole_0(u1_struct_0(esk2_0))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103, c_0_104]), c_0_70]), c_0_71]), c_0_57])]), c_0_87]), c_0_99])).
% 0.19/0.41  fof(c_0_107, plain, ![X27]:(~l1_pre_topc(X27)|l1_struct_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.41  cnf(c_0_108, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_105, c_0_106]), c_0_87])).
% 0.19/0.41  cnf(c_0_109, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_107])).
% 0.19/0.41  cnf(c_0_110, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_108, c_0_109]), c_0_71])]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 111
% 0.19/0.41  # Proof object clause steps            : 78
% 0.19/0.41  # Proof object formula steps           : 33
% 0.19/0.41  # Proof object conjectures             : 29
% 0.19/0.41  # Proof object clause conjectures      : 26
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 29
% 0.19/0.41  # Proof object initial formulas used   : 16
% 0.19/0.41  # Proof object generating inferences   : 43
% 0.19/0.41  # Proof object simplifying inferences  : 50
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 16
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 30
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 29
% 0.19/0.41  # Processed clauses                    : 263
% 0.19/0.41  # ...of these trivial                  : 0
% 0.19/0.41  # ...subsumed                          : 114
% 0.19/0.41  # ...remaining for further processing  : 149
% 0.19/0.41  # Other redundant clauses eliminated   : 35
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 11
% 0.19/0.41  # Backward-rewritten                   : 17
% 0.19/0.41  # Generated clauses                    : 579
% 0.19/0.41  # ...of the previous two non-trivial   : 488
% 0.19/0.41  # Contextual simplify-reflections      : 13
% 0.19/0.41  # Paramodulations                      : 532
% 0.19/0.41  # Factorizations                       : 14
% 0.19/0.41  # Equation resolutions                 : 35
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 118
% 0.19/0.41  #    Positive orientable unit clauses  : 10
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 3
% 0.19/0.41  #    Non-unit-clauses                  : 105
% 0.19/0.41  # Current number of unprocessed clauses: 235
% 0.19/0.41  # ...number of literals in the above   : 1455
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 29
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 4583
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1031
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 135
% 0.19/0.41  # Unit Clause-clause subsumption calls : 92
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 9
% 0.19/0.41  # BW rewrite match successes           : 1
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 14027
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.064 s
% 0.19/0.41  # System time              : 0.009 s
% 0.19/0.41  # Total time               : 0.072 s
% 0.19/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
