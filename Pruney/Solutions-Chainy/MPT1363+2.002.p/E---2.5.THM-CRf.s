%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:09 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 338 expanded)
%              Number of clauses        :   62 ( 131 expanded)
%              Number of leaves         :   18 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  390 (1819 expanded)
%              Number of equality atoms :   41 (  95 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_compts_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v2_compts_1(X2,X1)
                  & r1_tarski(X3,X2)
                  & v4_pre_topc(X3,X1) )
               => v2_compts_1(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_compts_1)).

fof(t11_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r1_tarski(X3,k2_struct_0(X2))
               => ( v2_compts_1(X3,X1)
                <=> ! [X4] :
                      ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X4 = X3
                       => v2_compts_1(X4,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t43_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( v4_pre_topc(X3,X2)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                    & v4_pre_topc(X4,X1)
                    & k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) = X3 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_pre_topc)).

fof(t10_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ( v1_compts_1(X1)
      <=> v2_compts_1(k2_struct_0(X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_compts_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t29_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => u1_struct_0(k1_pre_topc(X1,X2)) = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_pre_topc)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t17_compts_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( v1_compts_1(X1)
              & v4_pre_topc(X2,X1) )
           => v2_compts_1(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_compts_1)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v2_compts_1(X2,X1)
                    & r1_tarski(X3,X2)
                    & v4_pre_topc(X3,X1) )
                 => v2_compts_1(X3,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_compts_1])).

fof(c_0_19,plain,(
    ! [X45,X46,X47,X48] :
      ( ( ~ v2_compts_1(X47,X45)
        | ~ m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X46)))
        | X48 != X47
        | v2_compts_1(X48,X46)
        | ~ r1_tarski(X47,k2_struct_0(X46))
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ m1_pre_topc(X46,X45)
        | ~ l1_pre_topc(X45) )
      & ( m1_subset_1(esk2_3(X45,X46,X47),k1_zfmisc_1(u1_struct_0(X46)))
        | v2_compts_1(X47,X45)
        | ~ r1_tarski(X47,k2_struct_0(X46))
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ m1_pre_topc(X46,X45)
        | ~ l1_pre_topc(X45) )
      & ( esk2_3(X45,X46,X47) = X47
        | v2_compts_1(X47,X45)
        | ~ r1_tarski(X47,k2_struct_0(X46))
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ m1_pre_topc(X46,X45)
        | ~ l1_pre_topc(X45) )
      & ( ~ v2_compts_1(esk2_3(X45,X46,X47),X46)
        | v2_compts_1(X47,X45)
        | ~ r1_tarski(X47,k2_struct_0(X46))
        | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))
        | ~ m1_pre_topc(X46,X45)
        | ~ l1_pre_topc(X45) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).

fof(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & v2_compts_1(esk4_0,esk3_0)
    & r1_tarski(esk5_0,esk4_0)
    & v4_pre_topc(esk5_0,esk3_0)
    & ~ v2_compts_1(esk5_0,esk3_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_21,plain,(
    ! [X36,X37,X38] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_pre_topc(X37,X36)
      | ~ m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))
      | m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

fof(c_0_22,plain,(
    ! [X15] : m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_23,plain,(
    ! [X14] : k2_subset_1(X14) = X14 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_24,plain,
    ( m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
    | v2_compts_1(X3,X1)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_compts_1(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( esk2_3(X1,X2,X3) = X3
    | v2_compts_1(X3,X1)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_29,plain,(
    ! [X21,X22,X23] :
      ( ( X23 != k1_pre_topc(X21,X22)
        | k2_struct_0(X23) = X22
        | ~ v1_pre_topc(X23)
        | ~ m1_pre_topc(X23,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) )
      & ( k2_struct_0(X23) != X22
        | X23 = k1_pre_topc(X21,X22)
        | ~ v1_pre_topc(X23)
        | ~ m1_pre_topc(X23,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_30,plain,(
    ! [X25,X26] :
      ( ( v1_pre_topc(k1_pre_topc(X25,X26))
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) )
      & ( m1_pre_topc(k1_pre_topc(X25,X26),X25)
        | ~ l1_pre_topc(X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_31,plain,(
    ! [X24] :
      ( ~ l1_struct_0(X24)
      | k2_struct_0(X24) = u1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_32,plain,(
    ! [X27] :
      ( ~ l1_pre_topc(X27)
      | l1_struct_0(X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_33,plain,
    ( v2_compts_1(X3,X4)
    | ~ v2_compts_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | X3 != X1
    | ~ r1_tarski(X1,k2_struct_0(X4))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X4,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_34,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_36,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_37,plain,(
    ! [X7,X8] :
      ( ( r1_tarski(X7,X8)
        | X7 != X8 )
      & ( r1_tarski(X8,X7)
        | X7 != X8 )
      & ( ~ r1_tarski(X7,X8)
        | ~ r1_tarski(X8,X7)
        | X7 = X8 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_38,plain,(
    ! [X39,X40,X41,X43] :
      ( ( m1_subset_1(esk1_3(X39,X40,X41),k1_zfmisc_1(u1_struct_0(X39)))
        | ~ v4_pre_topc(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_pre_topc(X40,X39)
        | ~ l1_pre_topc(X39) )
      & ( v4_pre_topc(esk1_3(X39,X40,X41),X39)
        | ~ v4_pre_topc(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_pre_topc(X40,X39)
        | ~ l1_pre_topc(X39) )
      & ( k9_subset_1(u1_struct_0(X40),esk1_3(X39,X40,X41),k2_struct_0(X40)) = X41
        | ~ v4_pre_topc(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_pre_topc(X40,X39)
        | ~ l1_pre_topc(X39) )
      & ( ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X39)))
        | ~ v4_pre_topc(X43,X39)
        | k9_subset_1(u1_struct_0(X40),X43,k2_struct_0(X40)) != X41
        | v4_pre_topc(X41,X40)
        | ~ m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))
        | ~ m1_pre_topc(X40,X39)
        | ~ l1_pre_topc(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk2_3(esk3_0,X1,esk5_0),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r1_tarski(esk5_0,k2_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_40,negated_conjecture,
    ( esk2_3(esk3_0,X1,esk5_0) = esk5_0
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r1_tarski(esk5_0,k2_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_25]),c_0_26])]),c_0_27])).

cnf(c_0_41,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_42,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_43,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_44,plain,
    ( v2_compts_1(X3,X1)
    | ~ v2_compts_1(esk2_3(X1,X2,X3),X2)
    | ~ r1_tarski(X3,k2_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_45,plain,(
    ! [X44] :
      ( ( ~ v1_compts_1(X44)
        | v2_compts_1(k2_struct_0(X44),X44)
        | ~ l1_pre_topc(X44) )
      & ( ~ v2_compts_1(k2_struct_0(X44),X44)
        | v1_compts_1(X44)
        | ~ l1_pre_topc(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_compts_1])])])).

cnf(c_0_46,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_47,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

fof(c_0_48,plain,(
    ! [X28,X29] :
      ( ~ l1_pre_topc(X28)
      | ~ m1_pre_topc(X29,X28)
      | l1_pre_topc(X29) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_49,plain,
    ( v2_compts_1(X1,X2)
    | ~ v2_compts_1(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tarski(X1,k2_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]),c_0_34])).

cnf(c_0_50,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_51,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_52,plain,
    ( v4_pre_topc(X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_pre_topc(X1,X2)
    | k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3)) != X4
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

fof(c_0_53,plain,(
    ! [X9,X10] :
      ( ~ r1_tarski(X9,X10)
      | k3_xboole_0(X9,X10) = X9 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

fof(c_0_54,plain,(
    ! [X16,X17,X18] :
      ( ~ m1_subset_1(X18,k1_zfmisc_1(X16))
      | k9_subset_1(X16,X17,X18) = k3_xboole_0(X17,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r1_tarski(esk5_0,k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_56,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_41]),c_0_42]),c_0_43])).

cnf(c_0_57,negated_conjecture,
    ( ~ v2_compts_1(esk5_0,X1)
    | ~ m1_pre_topc(X1,esk3_0)
    | ~ r1_tarski(esk5_0,k2_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_40]),c_0_26]),c_0_25])]),c_0_27])).

cnf(c_0_58,plain,
    ( v1_compts_1(X1)
    | ~ v2_compts_1(k2_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_59,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

fof(c_0_60,plain,(
    ! [X34,X35] :
      ( ~ l1_pre_topc(X34)
      | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))
      | u1_struct_0(k1_pre_topc(X34,X35)) = X35 ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).

cnf(c_0_61,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,plain,
    ( v2_compts_1(u1_struct_0(X1),X1)
    | ~ v2_compts_1(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(u1_struct_0(X1),k2_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_63,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_64,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_65,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_66,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

fof(c_0_67,plain,(
    ! [X19,X20] :
      ( ( ~ m1_subset_1(X19,k1_zfmisc_1(X20))
        | r1_tarski(X19,X20) )
      & ( ~ r1_tarski(X19,X20)
        | m1_subset_1(X19,k1_zfmisc_1(X20)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_68,plain,(
    ! [X52,X53] :
      ( ~ l1_pre_topc(X52)
      | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
      | ~ v1_compts_1(X52)
      | ~ v4_pre_topc(X53,X52)
      | v2_compts_1(X53,X52) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_compts_1])])])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | ~ m1_pre_topc(k1_pre_topc(X1,X2),esk3_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_compts_1(esk5_0,k1_pre_topc(X1,X2))
    | ~ m1_pre_topc(k1_pre_topc(X1,X2),esk3_0)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tarski(esk5_0,X2) ),
    inference(spm,[status(thm)],[c_0_57,c_0_56])).

cnf(c_0_71,plain,
    ( v1_compts_1(X1)
    | ~ v2_compts_1(u1_struct_0(X1),X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_72,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_73,plain,
    ( l1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_61,c_0_43])).

cnf(c_0_74,plain,
    ( v2_compts_1(u1_struct_0(X1),X1)
    | ~ v2_compts_1(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_59]),c_0_63])]),c_0_61])).

cnf(c_0_75,plain,
    ( v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),X1)
    | ~ v4_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_59]),c_0_61])).

cnf(c_0_76,plain,
    ( k9_subset_1(X1,X2,X3) = X2
    | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
    | ~ r1_tarski(X2,X3) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_77,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_78,plain,
    ( v2_compts_1(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_compts_1(X1)
    | ~ v4_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_79,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk3_0,X1))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_43]),c_0_26])])).

cnf(c_0_80,negated_conjecture,
    ( ~ v2_compts_1(esk5_0,k1_pre_topc(esk3_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_43]),c_0_26])])).

cnf(c_0_81,plain,
    ( v1_compts_1(k1_pre_topc(X1,X2))
    | ~ v2_compts_1(X2,k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_83,plain,
    ( v2_compts_1(X1,k1_pre_topc(X2,X1))
    | ~ v2_compts_1(X1,X3)
    | ~ m1_pre_topc(k1_pre_topc(X2,X1),X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_74,c_0_72])).

cnf(c_0_84,plain,
    ( v4_pre_topc(X1,X2)
    | ~ v4_pre_topc(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ l1_pre_topc(X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_50])]),c_0_77]),c_0_34])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_compts_1(k1_pre_topc(esk3_0,X1))
    | ~ v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,X1))
    | ~ l1_pre_topc(k1_pre_topc(esk3_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])).

cnf(c_0_86,negated_conjecture,
    ( v1_compts_1(k1_pre_topc(esk3_0,esk4_0))
    | ~ v2_compts_1(esk4_0,k1_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_26])])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_88,negated_conjecture,
    ( v2_compts_1(esk4_0,k1_pre_topc(esk3_0,esk4_0))
    | ~ v2_compts_1(esk4_0,X1)
    | ~ m1_pre_topc(k1_pre_topc(esk3_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_82]),c_0_26])])).

cnf(c_0_89,negated_conjecture,
    ( v2_compts_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_90,negated_conjecture,
    ( v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,X1))
    | ~ v4_pre_topc(esk5_0,X2)
    | ~ m1_pre_topc(k1_pre_topc(esk3_0,X1),X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ r1_tarski(esk5_0,X1) ),
    inference(spm,[status(thm)],[c_0_84,c_0_79])).

cnf(c_0_91,negated_conjecture,
    ( ~ v2_compts_1(esk4_0,k1_pre_topc(esk3_0,esk4_0))
    | ~ v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,esk4_0))
    | ~ l1_pre_topc(k1_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_82]),c_0_87])])).

cnf(c_0_92,negated_conjecture,
    ( v2_compts_1(esk4_0,k1_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_43]),c_0_89]),c_0_26]),c_0_82])])).

cnf(c_0_93,negated_conjecture,
    ( v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,esk4_0))
    | ~ v4_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(k1_pre_topc(esk3_0,esk4_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_82]),c_0_87])])).

cnf(c_0_94,negated_conjecture,
    ( v4_pre_topc(esk5_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_95,negated_conjecture,
    ( ~ v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,esk4_0))
    | ~ l1_pre_topc(k1_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_92])])).

cnf(c_0_96,negated_conjecture,
    ( v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_43]),c_0_94]),c_0_26]),c_0_82])])).

cnf(c_0_97,negated_conjecture,
    ( ~ l1_pre_topc(k1_pre_topc(esk3_0,esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_73]),c_0_26]),c_0_82])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:50:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 2.57/2.75  # AutoSched0-Mode selected heuristic G_E___208_C18AMC_F1_SE_CS_SP_PS_S5PRR_RG_S04AN
% 2.57/2.75  # and selection function SelectComplexExceptUniqMaxHorn.
% 2.57/2.75  #
% 2.57/2.75  # Preprocessing time       : 0.030 s
% 2.57/2.75  # Presaturation interreduction done
% 2.57/2.75  
% 2.57/2.75  # Proof found!
% 2.57/2.75  # SZS status Theorem
% 2.57/2.75  # SZS output start CNFRefutation
% 2.57/2.75  fof(t18_compts_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v2_compts_1(X2,X1)&r1_tarski(X3,X2))&v4_pre_topc(X3,X1))=>v2_compts_1(X3,X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_compts_1)).
% 2.57/2.75  fof(t11_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(r1_tarski(X3,k2_struct_0(X2))=>(v2_compts_1(X3,X1)<=>![X4]:(m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))=>(X4=X3=>v2_compts_1(X4,X2)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_compts_1)).
% 2.57/2.75  fof(t39_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_pre_topc)).
% 2.57/2.75  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.57/2.75  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.57/2.75  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_pre_topc)).
% 2.57/2.75  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 2.57/2.75  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 2.57/2.75  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 2.57/2.75  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.57/2.75  fof(t43_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(v4_pre_topc(X3,X2)<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&v4_pre_topc(X4,X1))&k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))=X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_pre_topc)).
% 2.57/2.75  fof(t10_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>(v1_compts_1(X1)<=>v2_compts_1(k2_struct_0(X1),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_compts_1)).
% 2.57/2.75  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 2.57/2.75  fof(t28_xboole_1, axiom, ![X1, X2]:(r1_tarski(X1,X2)=>k3_xboole_0(X1,X2)=X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.57/2.75  fof(redefinition_k9_subset_1, axiom, ![X1, X2, X3]:(m1_subset_1(X3,k1_zfmisc_1(X1))=>k9_subset_1(X1,X2,X3)=k3_xboole_0(X2,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 2.57/2.75  fof(t29_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>u1_struct_0(k1_pre_topc(X1,X2))=X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_pre_topc)).
% 2.57/2.75  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.57/2.75  fof(t17_compts_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>((v1_compts_1(X1)&v4_pre_topc(X2,X1))=>v2_compts_1(X2,X1)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_compts_1)).
% 2.57/2.75  fof(c_0_18, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(((v2_compts_1(X2,X1)&r1_tarski(X3,X2))&v4_pre_topc(X3,X1))=>v2_compts_1(X3,X1)))))), inference(assume_negation,[status(cth)],[t18_compts_1])).
% 2.57/2.75  fof(c_0_19, plain, ![X45, X46, X47, X48]:((~v2_compts_1(X47,X45)|(~m1_subset_1(X48,k1_zfmisc_1(u1_struct_0(X46)))|(X48!=X47|v2_compts_1(X48,X46)))|~r1_tarski(X47,k2_struct_0(X46))|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~m1_pre_topc(X46,X45)|~l1_pre_topc(X45))&((m1_subset_1(esk2_3(X45,X46,X47),k1_zfmisc_1(u1_struct_0(X46)))|v2_compts_1(X47,X45)|~r1_tarski(X47,k2_struct_0(X46))|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~m1_pre_topc(X46,X45)|~l1_pre_topc(X45))&((esk2_3(X45,X46,X47)=X47|v2_compts_1(X47,X45)|~r1_tarski(X47,k2_struct_0(X46))|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~m1_pre_topc(X46,X45)|~l1_pre_topc(X45))&(~v2_compts_1(esk2_3(X45,X46,X47),X46)|v2_compts_1(X47,X45)|~r1_tarski(X47,k2_struct_0(X46))|~m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X45)))|~m1_pre_topc(X46,X45)|~l1_pre_topc(X45))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_compts_1])])])])])).
% 2.57/2.75  fof(c_0_20, negated_conjecture, ((v2_pre_topc(esk3_0)&l1_pre_topc(esk3_0))&(m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))&(((v2_compts_1(esk4_0,esk3_0)&r1_tarski(esk5_0,esk4_0))&v4_pre_topc(esk5_0,esk3_0))&~v2_compts_1(esk5_0,esk3_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 2.57/2.75  fof(c_0_21, plain, ![X36, X37, X38]:(~l1_pre_topc(X36)|(~m1_pre_topc(X37,X36)|(~m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X37)))|m1_subset_1(X38,k1_zfmisc_1(u1_struct_0(X36)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).
% 2.57/2.75  fof(c_0_22, plain, ![X15]:m1_subset_1(k2_subset_1(X15),k1_zfmisc_1(X15)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 2.57/2.75  fof(c_0_23, plain, ![X14]:k2_subset_1(X14)=X14, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 2.57/2.75  cnf(c_0_24, plain, (m1_subset_1(esk2_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X2)))|v2_compts_1(X3,X1)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.57/2.75  cnf(c_0_25, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.57/2.75  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.57/2.75  cnf(c_0_27, negated_conjecture, (~v2_compts_1(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.57/2.75  cnf(c_0_28, plain, (esk2_3(X1,X2,X3)=X3|v2_compts_1(X3,X1)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.57/2.75  fof(c_0_29, plain, ![X21, X22, X23]:((X23!=k1_pre_topc(X21,X22)|k2_struct_0(X23)=X22|(~v1_pre_topc(X23)|~m1_pre_topc(X23,X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))&(k2_struct_0(X23)!=X22|X23=k1_pre_topc(X21,X22)|(~v1_pre_topc(X23)|~m1_pre_topc(X23,X21))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|~l1_pre_topc(X21))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 2.57/2.75  fof(c_0_30, plain, ![X25, X26]:((v1_pre_topc(k1_pre_topc(X25,X26))|(~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))&(m1_pre_topc(k1_pre_topc(X25,X26),X25)|(~l1_pre_topc(X25)|~m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 2.57/2.75  fof(c_0_31, plain, ![X24]:(~l1_struct_0(X24)|k2_struct_0(X24)=u1_struct_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 2.57/2.75  fof(c_0_32, plain, ![X27]:(~l1_pre_topc(X27)|l1_struct_0(X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 2.57/2.75  cnf(c_0_33, plain, (v2_compts_1(X3,X4)|~v2_compts_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))|X3!=X1|~r1_tarski(X1,k2_struct_0(X4))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X4,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.57/2.75  cnf(c_0_34, plain, (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 2.57/2.75  cnf(c_0_35, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 2.57/2.75  cnf(c_0_36, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_23])).
% 2.57/2.75  fof(c_0_37, plain, ![X7, X8]:(((r1_tarski(X7,X8)|X7!=X8)&(r1_tarski(X8,X7)|X7!=X8))&(~r1_tarski(X7,X8)|~r1_tarski(X8,X7)|X7=X8)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 2.57/2.75  fof(c_0_38, plain, ![X39, X40, X41, X43]:((((m1_subset_1(esk1_3(X39,X40,X41),k1_zfmisc_1(u1_struct_0(X39)))|~v4_pre_topc(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~m1_pre_topc(X40,X39)|~l1_pre_topc(X39))&(v4_pre_topc(esk1_3(X39,X40,X41),X39)|~v4_pre_topc(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~m1_pre_topc(X40,X39)|~l1_pre_topc(X39)))&(k9_subset_1(u1_struct_0(X40),esk1_3(X39,X40,X41),k2_struct_0(X40))=X41|~v4_pre_topc(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~m1_pre_topc(X40,X39)|~l1_pre_topc(X39)))&(~m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X39)))|~v4_pre_topc(X43,X39)|k9_subset_1(u1_struct_0(X40),X43,k2_struct_0(X40))!=X41|v4_pre_topc(X41,X40)|~m1_subset_1(X41,k1_zfmisc_1(u1_struct_0(X40)))|~m1_pre_topc(X40,X39)|~l1_pre_topc(X39))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t43_pre_topc])])])])])).
% 2.57/2.75  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk2_3(esk3_0,X1,esk5_0),k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X1,esk3_0)|~r1_tarski(esk5_0,k2_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])]), c_0_27])).
% 2.57/2.75  cnf(c_0_40, negated_conjecture, (esk2_3(esk3_0,X1,esk5_0)=esk5_0|~m1_pre_topc(X1,esk3_0)|~r1_tarski(esk5_0,k2_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_25]), c_0_26])]), c_0_27])).
% 2.57/2.75  cnf(c_0_41, plain, (k2_struct_0(X1)=X3|X1!=k1_pre_topc(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 2.57/2.75  cnf(c_0_42, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.57/2.75  cnf(c_0_43, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 2.57/2.75  cnf(c_0_44, plain, (v2_compts_1(X3,X1)|~v2_compts_1(esk2_3(X1,X2,X3),X2)|~r1_tarski(X3,k2_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 2.57/2.75  fof(c_0_45, plain, ![X44]:((~v1_compts_1(X44)|v2_compts_1(k2_struct_0(X44),X44)|~l1_pre_topc(X44))&(~v2_compts_1(k2_struct_0(X44),X44)|v1_compts_1(X44)|~l1_pre_topc(X44))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t10_compts_1])])])).
% 2.57/2.75  cnf(c_0_46, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 2.57/2.75  cnf(c_0_47, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_32])).
% 2.57/2.75  fof(c_0_48, plain, ![X28, X29]:(~l1_pre_topc(X28)|(~m1_pre_topc(X29,X28)|l1_pre_topc(X29))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 2.57/2.75  cnf(c_0_49, plain, (v2_compts_1(X1,X2)|~v2_compts_1(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r1_tarski(X1,k2_struct_0(X2))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_33]), c_0_34])).
% 2.57/2.75  cnf(c_0_50, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_35, c_0_36])).
% 2.57/2.75  cnf(c_0_51, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_37])).
% 2.57/2.75  cnf(c_0_52, plain, (v4_pre_topc(X4,X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v4_pre_topc(X1,X2)|k9_subset_1(u1_struct_0(X3),X1,k2_struct_0(X3))!=X4|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 2.57/2.75  fof(c_0_53, plain, ![X9, X10]:(~r1_tarski(X9,X10)|k3_xboole_0(X9,X10)=X9), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).
% 2.57/2.75  fof(c_0_54, plain, ![X16, X17, X18]:(~m1_subset_1(X18,k1_zfmisc_1(X16))|k9_subset_1(X16,X17,X18)=k3_xboole_0(X17,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).
% 2.57/2.75  cnf(c_0_55, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(X1)))|~m1_pre_topc(X1,esk3_0)|~r1_tarski(esk5_0,k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_39, c_0_40])).
% 2.57/2.75  cnf(c_0_56, plain, (k2_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_41]), c_0_42]), c_0_43])).
% 2.57/2.75  cnf(c_0_57, negated_conjecture, (~v2_compts_1(esk5_0,X1)|~m1_pre_topc(X1,esk3_0)|~r1_tarski(esk5_0,k2_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_40]), c_0_26]), c_0_25])]), c_0_27])).
% 2.57/2.75  cnf(c_0_58, plain, (v1_compts_1(X1)|~v2_compts_1(k2_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 2.57/2.75  cnf(c_0_59, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 2.57/2.75  fof(c_0_60, plain, ![X34, X35]:(~l1_pre_topc(X34)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X34)))|u1_struct_0(k1_pre_topc(X34,X35))=X35)), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t29_pre_topc])])])).
% 2.57/2.75  cnf(c_0_61, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 2.57/2.75  cnf(c_0_62, plain, (v2_compts_1(u1_struct_0(X1),X1)|~v2_compts_1(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~r1_tarski(u1_struct_0(X1),k2_struct_0(X1))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 2.57/2.75  cnf(c_0_63, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_51])).
% 2.57/2.75  cnf(c_0_64, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),X1)|~v4_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(er,[status(thm)],[c_0_52])).
% 2.57/2.75  cnf(c_0_65, plain, (k3_xboole_0(X1,X2)=X1|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 2.57/2.75  cnf(c_0_66, plain, (k9_subset_1(X2,X3,X1)=k3_xboole_0(X3,X1)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 2.57/2.75  fof(c_0_67, plain, ![X19, X20]:((~m1_subset_1(X19,k1_zfmisc_1(X20))|r1_tarski(X19,X20))&(~r1_tarski(X19,X20)|m1_subset_1(X19,k1_zfmisc_1(X20)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 2.57/2.75  fof(c_0_68, plain, ![X52, X53]:(~l1_pre_topc(X52)|(~m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))|(~v1_compts_1(X52)|~v4_pre_topc(X53,X52)|v2_compts_1(X53,X52)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t17_compts_1])])])).
% 2.57/2.75  cnf(c_0_69, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))|~m1_pre_topc(k1_pre_topc(X1,X2),esk3_0)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_55, c_0_56])).
% 2.57/2.75  cnf(c_0_70, negated_conjecture, (~v2_compts_1(esk5_0,k1_pre_topc(X1,X2))|~m1_pre_topc(k1_pre_topc(X1,X2),esk3_0)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~r1_tarski(esk5_0,X2)), inference(spm,[status(thm)],[c_0_57, c_0_56])).
% 2.57/2.75  cnf(c_0_71, plain, (v1_compts_1(X1)|~v2_compts_1(u1_struct_0(X1),X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 2.57/2.75  cnf(c_0_72, plain, (u1_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_60])).
% 2.57/2.75  cnf(c_0_73, plain, (l1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_61, c_0_43])).
% 2.57/2.75  cnf(c_0_74, plain, (v2_compts_1(u1_struct_0(X1),X1)|~v2_compts_1(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_59]), c_0_63])]), c_0_61])).
% 2.57/2.75  cnf(c_0_75, plain, (v4_pre_topc(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),X1)|~v4_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~m1_subset_1(k9_subset_1(u1_struct_0(X1),X2,u1_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_59]), c_0_61])).
% 2.57/2.75  cnf(c_0_76, plain, (k9_subset_1(X1,X2,X3)=X2|~m1_subset_1(X3,k1_zfmisc_1(X1))|~r1_tarski(X2,X3)), inference(spm,[status(thm)],[c_0_65, c_0_66])).
% 2.57/2.75  cnf(c_0_77, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_67])).
% 2.57/2.75  cnf(c_0_78, plain, (v2_compts_1(X2,X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~v1_compts_1(X1)|~v4_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_68])).
% 2.57/2.75  cnf(c_0_79, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk3_0,X1))))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_43]), c_0_26])])).
% 2.57/2.75  cnf(c_0_80, negated_conjecture, (~v2_compts_1(esk5_0,k1_pre_topc(esk3_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk5_0,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_43]), c_0_26])])).
% 2.57/2.75  cnf(c_0_81, plain, (v1_compts_1(k1_pre_topc(X1,X2))|~v2_compts_1(X2,k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71, c_0_72]), c_0_73])).
% 2.57/2.75  cnf(c_0_82, negated_conjecture, (m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.57/2.75  cnf(c_0_83, plain, (v2_compts_1(X1,k1_pre_topc(X2,X1))|~v2_compts_1(X1,X3)|~m1_pre_topc(k1_pre_topc(X2,X1),X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_74, c_0_72])).
% 2.57/2.75  cnf(c_0_84, plain, (v4_pre_topc(X1,X2)|~v4_pre_topc(X1,X3)|~m1_pre_topc(X2,X3)|~l1_pre_topc(X3)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_50])]), c_0_77]), c_0_34])).
% 2.57/2.75  cnf(c_0_85, negated_conjecture, (~v1_compts_1(k1_pre_topc(esk3_0,X1))|~v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,X1))|~l1_pre_topc(k1_pre_topc(esk3_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk5_0,X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_80])).
% 2.57/2.75  cnf(c_0_86, negated_conjecture, (v1_compts_1(k1_pre_topc(esk3_0,esk4_0))|~v2_compts_1(esk4_0,k1_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_82]), c_0_26])])).
% 2.57/2.75  cnf(c_0_87, negated_conjecture, (r1_tarski(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.57/2.75  cnf(c_0_88, negated_conjecture, (v2_compts_1(esk4_0,k1_pre_topc(esk3_0,esk4_0))|~v2_compts_1(esk4_0,X1)|~m1_pre_topc(k1_pre_topc(esk3_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_82]), c_0_26])])).
% 2.57/2.75  cnf(c_0_89, negated_conjecture, (v2_compts_1(esk4_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.57/2.75  cnf(c_0_90, negated_conjecture, (v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,X1))|~v4_pre_topc(esk5_0,X2)|~m1_pre_topc(k1_pre_topc(esk3_0,X1),X2)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))|~r1_tarski(esk5_0,X1)), inference(spm,[status(thm)],[c_0_84, c_0_79])).
% 2.57/2.75  cnf(c_0_91, negated_conjecture, (~v2_compts_1(esk4_0,k1_pre_topc(esk3_0,esk4_0))|~v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,esk4_0))|~l1_pre_topc(k1_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_86]), c_0_82]), c_0_87])])).
% 2.57/2.75  cnf(c_0_92, negated_conjecture, (v2_compts_1(esk4_0,k1_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_43]), c_0_89]), c_0_26]), c_0_82])])).
% 2.57/2.75  cnf(c_0_93, negated_conjecture, (v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,esk4_0))|~v4_pre_topc(esk5_0,X1)|~m1_pre_topc(k1_pre_topc(esk3_0,esk4_0),X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90, c_0_82]), c_0_87])])).
% 2.57/2.75  cnf(c_0_94, negated_conjecture, (v4_pre_topc(esk5_0,esk3_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 2.57/2.75  cnf(c_0_95, negated_conjecture, (~v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,esk4_0))|~l1_pre_topc(k1_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91, c_0_92])])).
% 2.57/2.75  cnf(c_0_96, negated_conjecture, (v4_pre_topc(esk5_0,k1_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93, c_0_43]), c_0_94]), c_0_26]), c_0_82])])).
% 2.57/2.75  cnf(c_0_97, negated_conjecture, (~l1_pre_topc(k1_pre_topc(esk3_0,esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96])])).
% 2.57/2.75  cnf(c_0_98, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97, c_0_73]), c_0_26]), c_0_82])]), ['proof']).
% 2.57/2.75  # SZS output end CNFRefutation
% 2.57/2.75  # Proof object total steps             : 99
% 2.57/2.75  # Proof object clause steps            : 62
% 2.57/2.75  # Proof object formula steps           : 37
% 2.57/2.75  # Proof object conjectures             : 29
% 2.57/2.75  # Proof object clause conjectures      : 26
% 2.57/2.75  # Proof object formula conjectures     : 3
% 2.57/2.75  # Proof object initial clauses used    : 28
% 2.57/2.75  # Proof object initial formulas used   : 18
% 2.57/2.75  # Proof object generating inferences   : 27
% 2.57/2.75  # Proof object simplifying inferences  : 56
% 2.57/2.75  # Training examples: 0 positive, 0 negative
% 2.57/2.75  # Parsed axioms                        : 22
% 2.57/2.75  # Removed by relevancy pruning/SinE    : 0
% 2.57/2.75  # Initial clauses                      : 44
% 2.57/2.75  # Removed in clause preprocessing      : 1
% 2.57/2.75  # Initial clauses in saturation        : 43
% 2.57/2.75  # Processed clauses                    : 19482
% 2.57/2.75  # ...of these trivial                  : 46
% 2.57/2.75  # ...subsumed                          : 16321
% 2.57/2.75  # ...remaining for further processing  : 3115
% 2.57/2.75  # Other redundant clauses eliminated   : 9
% 2.57/2.75  # Clauses deleted for lack of memory   : 0
% 2.57/2.75  # Backward-subsumed                    : 433
% 2.57/2.75  # Backward-rewritten                   : 86
% 2.57/2.75  # Generated clauses                    : 102117
% 2.57/2.75  # ...of the previous two non-trivial   : 98133
% 2.57/2.75  # Contextual simplify-reflections      : 614
% 2.57/2.75  # Paramodulations                      : 102108
% 2.57/2.75  # Factorizations                       : 0
% 2.57/2.75  # Equation resolutions                 : 9
% 2.57/2.75  # Propositional unsat checks           : 0
% 2.57/2.75  #    Propositional check models        : 0
% 2.57/2.75  #    Propositional check unsatisfiable : 0
% 2.57/2.75  #    Propositional clauses             : 0
% 2.57/2.75  #    Propositional clauses after purity: 0
% 2.57/2.75  #    Propositional unsat core size     : 0
% 2.57/2.75  #    Propositional preprocessing time  : 0.000
% 2.57/2.75  #    Propositional encoding time       : 0.000
% 2.57/2.75  #    Propositional solver time         : 0.000
% 2.57/2.75  #    Success case prop preproc time    : 0.000
% 2.57/2.75  #    Success case prop encoding time   : 0.000
% 2.57/2.75  #    Success case prop solver time     : 0.000
% 2.57/2.75  # Current number of processed clauses  : 2545
% 2.57/2.75  #    Positive orientable unit clauses  : 23
% 2.57/2.75  #    Positive unorientable unit clauses: 1
% 2.57/2.75  #    Negative unit clauses             : 7
% 2.57/2.75  #    Non-unit-clauses                  : 2514
% 2.57/2.75  # Current number of unprocessed clauses: 77349
% 2.57/2.75  # ...number of literals in the above   : 811981
% 2.57/2.75  # Current number of archived formulas  : 0
% 2.57/2.75  # Current number of archived clauses   : 562
% 2.57/2.75  # Clause-clause subsumption calls (NU) : 2249600
% 2.57/2.75  # Rec. Clause-clause subsumption calls : 76969
% 2.57/2.75  # Non-unit clause-clause subsumptions  : 11189
% 2.57/2.75  # Unit Clause-clause subsumption calls : 11479
% 2.57/2.75  # Rewrite failures with RHS unbound    : 0
% 2.57/2.75  # BW rewrite match attempts            : 28
% 2.57/2.75  # BW rewrite match successes           : 18
% 2.57/2.75  # Condensation attempts                : 0
% 2.57/2.75  # Condensation successes               : 0
% 2.57/2.75  # Termbank termtop insertions          : 4033162
% 2.57/2.76  
% 2.57/2.76  # -------------------------------------------------
% 2.57/2.76  # User time                : 2.363 s
% 2.57/2.76  # System time              : 0.054 s
% 2.57/2.76  # Total time               : 2.417 s
% 2.57/2.76  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
