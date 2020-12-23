%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:58 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 905 expanded)
%              Number of clauses        :   63 ( 346 expanded)
%              Number of leaves         :   13 ( 222 expanded)
%              Depth                    :   21
%              Number of atoms          :  401 (6983 expanded)
%              Number of equality atoms :   29 ( 136 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t23_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( m1_pre_topc(X2,X3)
                   => ( ( r1_tsep_1(X2,X4)
                        & r1_tsep_1(X4,X2) )
                      | ( ~ r1_tsep_1(X3,X4)
                        & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tmap_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t4_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( r1_tarski(u1_struct_0(X2),u1_struct_0(X3))
              <=> m1_pre_topc(X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(dt_k1_tsep_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X2,X1)
        & ~ v2_struct_0(X3)
        & m1_pre_topc(X3,X1) )
     => ( ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
        & v1_pre_topc(k1_tsep_1(X1,X2,X3))
        & m1_pre_topc(k1_tsep_1(X1,X2,X3),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

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

fof(d2_tsep_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & v1_pre_topc(X4)
                    & m1_pre_topc(X4,X1) )
                 => ( X4 = k1_tsep_1(X1,X2,X3)
                  <=> u1_struct_0(X4) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(t11_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X1,X2),X3)
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ( m1_pre_topc(X2,X3)
                     => ( ( r1_tsep_1(X2,X4)
                          & r1_tsep_1(X4,X2) )
                        | ( ~ r1_tsep_1(X3,X4)
                          & ~ r1_tsep_1(X4,X3) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t23_tmap_1])).

fof(c_0_14,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_15,plain,(
    ! [X23,X24] :
      ( ~ l1_pre_topc(X23)
      | ~ m1_pre_topc(X24,X23)
      | l1_pre_topc(X24) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_16,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & m1_pre_topc(esk5_0,esk4_0)
    & ~ v2_struct_0(esk6_0)
    & m1_pre_topc(esk6_0,esk4_0)
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk4_0)
    & m1_pre_topc(esk5_0,esk6_0)
    & ( ~ r1_tsep_1(esk5_0,esk7_0)
      | ~ r1_tsep_1(esk7_0,esk5_0) )
    & ( r1_tsep_1(esk6_0,esk7_0)
      | r1_tsep_1(esk7_0,esk6_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_17,plain,(
    ! [X36,X37,X38] :
      ( ( ~ r1_tarski(u1_struct_0(X37),u1_struct_0(X38))
        | m1_pre_topc(X37,X38)
        | ~ m1_pre_topc(X38,X36)
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) )
      & ( ~ m1_pre_topc(X37,X38)
        | r1_tarski(u1_struct_0(X37),u1_struct_0(X38))
        | ~ m1_pre_topc(X38,X36)
        | ~ m1_pre_topc(X37,X36)
        | ~ v2_pre_topc(X36)
        | ~ l1_pre_topc(X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X31,X32,X33] :
      ( ( ~ v2_struct_0(k1_tsep_1(X31,X32,X33))
        | v2_struct_0(X31)
        | ~ l1_pre_topc(X31)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X31)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X31) )
      & ( v1_pre_topc(k1_tsep_1(X31,X32,X33))
        | v2_struct_0(X31)
        | ~ l1_pre_topc(X31)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X31)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X31) )
      & ( m1_pre_topc(k1_tsep_1(X31,X32,X33),X31)
        | v2_struct_0(X31)
        | ~ l1_pre_topc(X31)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X31)
        | v2_struct_0(X33)
        | ~ m1_pre_topc(X33,X31) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).

cnf(c_0_20,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X14,X15,X16,X18,X20] :
      ( ( r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk1_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(X16,u1_pre_topc(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk1_3(X14,X15,X16),u1_pre_topc(X14))
        | ~ r2_hidden(X16,u1_pre_topc(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( X16 = k9_subset_1(u1_struct_0(X15),esk1_3(X14,X15,X16),k2_struct_0(X15))
        | ~ r2_hidden(X16,u1_pre_topc(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(X18,u1_pre_topc(X14))
        | X16 != k9_subset_1(u1_struct_0(X15),X18,k2_struct_0(X15))
        | r2_hidden(X16,u1_pre_topc(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_2(X14,X15),k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(X20,u1_pre_topc(X14))
        | esk2_2(X14,X15) != k9_subset_1(u1_struct_0(X15),X20,k2_struct_0(X15))
        | ~ r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk3_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))
        | r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))
        | ~ r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk3_2(X14,X15),u1_pre_topc(X14))
        | r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))
        | ~ r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( esk2_2(X14,X15) = k9_subset_1(u1_struct_0(X15),esk3_2(X14,X15),k2_struct_0(X15))
        | r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))
        | ~ r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

cnf(c_0_26,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_28,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_29,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_31,plain,
    ( m1_pre_topc(X1,X1)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_33,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_34,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk6_0,X1,esk5_0),esk6_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_21]),c_0_32]),c_0_22])])).

fof(c_0_36,plain,(
    ! [X13] :
      ( ~ l1_struct_0(X13)
      | k2_struct_0(X13) = u1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_37,plain,(
    ! [X22] :
      ( ~ l1_pre_topc(X22)
      | l1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_38,plain,(
    ! [X25,X26,X27,X28] :
      ( ( X28 != k1_tsep_1(X25,X26,X27)
        | u1_struct_0(X28) = k2_xboole_0(u1_struct_0(X26),u1_struct_0(X27))
        | v2_struct_0(X28)
        | ~ v1_pre_topc(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25) )
      & ( u1_struct_0(X28) != k2_xboole_0(u1_struct_0(X26),u1_struct_0(X27))
        | X28 = k1_tsep_1(X25,X26,X27)
        | v2_struct_0(X28)
        | ~ v1_pre_topc(X28)
        | ~ m1_pre_topc(X28,X25)
        | v2_struct_0(X27)
        | ~ m1_pre_topc(X27,X25)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X25)
        | v2_struct_0(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

cnf(c_0_39,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_33,c_0_20])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_28])).

cnf(c_0_41,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_43,plain,
    ( u1_struct_0(X1) = k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))
    | v2_struct_0(X1)
    | v2_struct_0(X4)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | X1 != k1_tsep_1(X2,X3,X4)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_46,plain,(
    ! [X34,X35] :
      ( ~ l1_struct_0(X34)
      | ~ l1_struct_0(X35)
      | ~ r1_tsep_1(X34,X35)
      | r1_tsep_1(X35,X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_47,negated_conjecture,
    ( r1_tarski(k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),k2_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_30])])).

cnf(c_0_48,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_49,plain,(
    ! [X7,X8,X9] :
      ( ~ r1_tarski(k2_xboole_0(X7,X8),X9)
      | r1_tarski(X7,X9) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).

cnf(c_0_50,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]),c_0_26]),c_0_44]),c_0_45])).

cnf(c_0_51,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_52,negated_conjecture,
    ( r1_tsep_1(esk6_0,esk7_0)
    | r1_tsep_1(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,negated_conjecture,
    ( r1_tarski(k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_30])])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_40]),c_0_30])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(k2_xboole_0(X1,X2),X3) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk5_0)) = u1_struct_0(k1_tsep_1(esk6_0,X1,esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_27]),c_0_30])]),c_0_29]),c_0_28])).

cnf(c_0_58,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0)
    | ~ l1_struct_0(esk7_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_53]),c_0_22])])).

cnf(c_0_60,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_61,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_48]),c_0_55])])).

cnf(c_0_62,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_24])).

cnf(c_0_63,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk6_0),u1_struct_0(esk5_0)) = u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_35]),c_0_28])).

fof(c_0_64,plain,(
    ! [X29,X30] :
      ( ( ~ r1_tsep_1(X29,X30)
        | r1_xboole_0(u1_struct_0(X29),u1_struct_0(X30))
        | ~ l1_struct_0(X30)
        | ~ l1_struct_0(X29) )
      & ( ~ r1_xboole_0(u1_struct_0(X29),u1_struct_0(X30))
        | r1_tsep_1(X29,X30)
        | ~ l1_struct_0(X30)
        | ~ l1_struct_0(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_65,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_42]),c_0_59])])).

cnf(c_0_66,negated_conjecture,
    ( u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)) = u1_struct_0(esk6_0)
    | ~ r1_tarski(u1_struct_0(esk6_0),u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk6_0),u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0))) ),
    inference(spm,[status(thm)],[c_0_62,c_0_63])).

cnf(c_0_68,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_42]),c_0_30])])).

fof(c_0_70,plain,(
    ! [X10,X11,X12] :
      ( ( r1_xboole_0(X10,k2_xboole_0(X11,X12))
        | ~ r1_xboole_0(X10,X11)
        | ~ r1_xboole_0(X10,X12) )
      & ( r1_xboole_0(X10,X11)
        | ~ r1_xboole_0(X10,k2_xboole_0(X11,X12)) )
      & ( r1_xboole_0(X10,X12)
        | ~ r1_xboole_0(X10,k2_xboole_0(X11,X12)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_71,negated_conjecture,
    ( u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)) = u1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67])])).

cnf(c_0_72,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk6_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_73,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

cnf(c_0_74,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk6_0),u1_struct_0(esk5_0)) = u1_struct_0(esk6_0) ),
    inference(rw,[status(thm)],[c_0_63,c_0_71])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_42]),c_0_30])])).

cnf(c_0_76,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk5_0))
    | ~ r1_xboole_0(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_42]),c_0_59])])).

cnf(c_0_78,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_79,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_81,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_80]),c_0_22])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_42]),c_0_82])])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk7_0)
    | ~ r1_tsep_1(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_85,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_42]),c_0_59])])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85])])).

cnf(c_0_87,negated_conjecture,
    ( ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_85]),c_0_86])).

cnf(c_0_88,negated_conjecture,
    ( ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_42]),c_0_82])])).

cnf(c_0_89,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_42]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:22:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.21/0.49  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.21/0.49  # and selection function SelectNewComplexAHPNS.
% 0.21/0.49  #
% 0.21/0.49  # Preprocessing time       : 0.029 s
% 0.21/0.49  
% 0.21/0.49  # Proof found!
% 0.21/0.49  # SZS status Theorem
% 0.21/0.49  # SZS output start CNFRefutation
% 0.21/0.49  fof(t23_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 0.21/0.49  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.21/0.49  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.21/0.49  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.21/0.49  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.21/0.49  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.21/0.49  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.21/0.49  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.21/0.49  fof(d2_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k1_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 0.21/0.49  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.21/0.49  fof(t11_xboole_1, axiom, ![X1, X2, X3]:(r1_tarski(k2_xboole_0(X1,X2),X3)=>r1_tarski(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 0.21/0.49  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.21/0.49  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.21/0.49  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))))))))), inference(assume_negation,[status(cth)],[t23_tmap_1])).
% 0.21/0.49  fof(c_0_14, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.21/0.49  fof(c_0_15, plain, ![X23, X24]:(~l1_pre_topc(X23)|(~m1_pre_topc(X24,X23)|l1_pre_topc(X24))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.21/0.49  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk4_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk4_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk4_0))&(m1_pre_topc(esk5_0,esk6_0)&((~r1_tsep_1(esk5_0,esk7_0)|~r1_tsep_1(esk7_0,esk5_0))&(r1_tsep_1(esk6_0,esk7_0)|r1_tsep_1(esk7_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.21/0.49  fof(c_0_17, plain, ![X36, X37, X38]:((~r1_tarski(u1_struct_0(X37),u1_struct_0(X38))|m1_pre_topc(X37,X38)|~m1_pre_topc(X38,X36)|~m1_pre_topc(X37,X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))&(~m1_pre_topc(X37,X38)|r1_tarski(u1_struct_0(X37),u1_struct_0(X38))|~m1_pre_topc(X38,X36)|~m1_pre_topc(X37,X36)|(~v2_pre_topc(X36)|~l1_pre_topc(X36)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.21/0.49  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.49  fof(c_0_19, plain, ![X31, X32, X33]:(((~v2_struct_0(k1_tsep_1(X31,X32,X33))|(v2_struct_0(X31)|~l1_pre_topc(X31)|v2_struct_0(X32)|~m1_pre_topc(X32,X31)|v2_struct_0(X33)|~m1_pre_topc(X33,X31)))&(v1_pre_topc(k1_tsep_1(X31,X32,X33))|(v2_struct_0(X31)|~l1_pre_topc(X31)|v2_struct_0(X32)|~m1_pre_topc(X32,X31)|v2_struct_0(X33)|~m1_pre_topc(X33,X31))))&(m1_pre_topc(k1_tsep_1(X31,X32,X33),X31)|(v2_struct_0(X31)|~l1_pre_topc(X31)|v2_struct_0(X32)|~m1_pre_topc(X32,X31)|v2_struct_0(X33)|~m1_pre_topc(X33,X31)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.21/0.49  cnf(c_0_20, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.21/0.49  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_23, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.21/0.49  cnf(c_0_24, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.21/0.49  fof(c_0_25, plain, ![X14, X15, X16, X18, X20]:(((r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))&((((m1_subset_1(esk1_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14)))|~r2_hidden(X16,u1_pre_topc(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))&(r2_hidden(esk1_3(X14,X15,X16),u1_pre_topc(X14))|~r2_hidden(X16,u1_pre_topc(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14)))&(X16=k9_subset_1(u1_struct_0(X15),esk1_3(X14,X15,X16),k2_struct_0(X15))|~r2_hidden(X16,u1_pre_topc(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14)))&(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X14)))|~r2_hidden(X18,u1_pre_topc(X14))|X16!=k9_subset_1(u1_struct_0(X15),X18,k2_struct_0(X15))|r2_hidden(X16,u1_pre_topc(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))))&((m1_subset_1(esk2_2(X14,X15),k1_zfmisc_1(u1_struct_0(X15)))|~r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))&((~r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X14)))|~r2_hidden(X20,u1_pre_topc(X14))|esk2_2(X14,X15)!=k9_subset_1(u1_struct_0(X15),X20,k2_struct_0(X15)))|~r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))&(((m1_subset_1(esk3_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))|r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))|~r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))&(r2_hidden(esk3_2(X14,X15),u1_pre_topc(X14))|r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))|~r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14)))&(esk2_2(X14,X15)=k9_subset_1(u1_struct_0(X15),esk3_2(X14,X15),k2_struct_0(X15))|r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))|~r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.21/0.49  cnf(c_0_26, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.49  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.21/0.49  cnf(c_0_31, plain, (m1_pre_topc(X1,X1)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.21/0.49  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_33, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.21/0.49  cnf(c_0_34, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk6_0,X1,esk5_0),esk6_0)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30])])).
% 0.21/0.49  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_21]), c_0_32]), c_0_22])])).
% 0.21/0.49  fof(c_0_36, plain, ![X13]:(~l1_struct_0(X13)|k2_struct_0(X13)=u1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.21/0.49  fof(c_0_37, plain, ![X22]:(~l1_pre_topc(X22)|l1_struct_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.21/0.49  fof(c_0_38, plain, ![X25, X26, X27, X28]:((X28!=k1_tsep_1(X25,X26,X27)|u1_struct_0(X28)=k2_xboole_0(u1_struct_0(X26),u1_struct_0(X27))|(v2_struct_0(X28)|~v1_pre_topc(X28)|~m1_pre_topc(X28,X25))|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~l1_pre_topc(X25)))&(u1_struct_0(X28)!=k2_xboole_0(u1_struct_0(X26),u1_struct_0(X27))|X28=k1_tsep_1(X25,X26,X27)|(v2_struct_0(X28)|~v1_pre_topc(X28)|~m1_pre_topc(X28,X25))|(v2_struct_0(X27)|~m1_pre_topc(X27,X25))|(v2_struct_0(X26)|~m1_pre_topc(X26,X25))|(v2_struct_0(X25)|~l1_pre_topc(X25)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).
% 0.21/0.49  cnf(c_0_39, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_33, c_0_20])).
% 0.21/0.49  cnf(c_0_40, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_28])).
% 0.21/0.49  cnf(c_0_41, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.21/0.49  cnf(c_0_42, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.21/0.49  cnf(c_0_43, plain, (u1_struct_0(X1)=k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k1_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.21/0.49  cnf(c_0_44, plain, (v1_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.49  cnf(c_0_45, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.21/0.49  fof(c_0_46, plain, ![X34, X35]:(~l1_struct_0(X34)|~l1_struct_0(X35)|(~r1_tsep_1(X34,X35)|r1_tsep_1(X35,X34))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.21/0.49  cnf(c_0_47, negated_conjecture, (r1_tarski(k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),k2_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_30])])).
% 0.21/0.49  cnf(c_0_48, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.21/0.49  fof(c_0_49, plain, ![X7, X8, X9]:(~r1_tarski(k2_xboole_0(X7,X8),X9)|r1_tarski(X7,X9)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_xboole_1])])).
% 0.21/0.49  cnf(c_0_50, plain, (u1_struct_0(k1_tsep_1(X1,X2,X3))=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_43]), c_0_26]), c_0_44]), c_0_45])).
% 0.21/0.49  cnf(c_0_51, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.21/0.49  cnf(c_0_52, negated_conjecture, (r1_tsep_1(esk6_0,esk7_0)|r1_tsep_1(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_53, negated_conjecture, (m1_pre_topc(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_54, negated_conjecture, (r1_tarski(k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_30])])).
% 0.21/0.49  cnf(c_0_55, negated_conjecture, (l1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_40]), c_0_30])])).
% 0.21/0.49  cnf(c_0_56, plain, (r1_tarski(X1,X3)|~r1_tarski(k2_xboole_0(X1,X2),X3)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.21/0.49  cnf(c_0_57, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk5_0))=u1_struct_0(k1_tsep_1(esk6_0,X1,esk5_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50, c_0_27]), c_0_30])]), c_0_29]), c_0_28])).
% 0.21/0.49  cnf(c_0_58, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)|~l1_struct_0(esk7_0)|~l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.21/0.49  cnf(c_0_59, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_53]), c_0_22])])).
% 0.21/0.49  cnf(c_0_60, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.21/0.49  cnf(c_0_61, negated_conjecture, (r1_tarski(u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_48]), c_0_55])])).
% 0.21/0.49  cnf(c_0_62, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(spm,[status(thm)],[c_0_56, c_0_24])).
% 0.21/0.49  cnf(c_0_63, negated_conjecture, (k2_xboole_0(u1_struct_0(esk6_0),u1_struct_0(esk5_0))=u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_35]), c_0_28])).
% 0.21/0.49  fof(c_0_64, plain, ![X29, X30]:((~r1_tsep_1(X29,X30)|r1_xboole_0(u1_struct_0(X29),u1_struct_0(X30))|~l1_struct_0(X30)|~l1_struct_0(X29))&(~r1_xboole_0(u1_struct_0(X29),u1_struct_0(X30))|r1_tsep_1(X29,X30)|~l1_struct_0(X30)|~l1_struct_0(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.21/0.49  cnf(c_0_65, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)|~l1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_42]), c_0_59])])).
% 0.21/0.49  cnf(c_0_66, negated_conjecture, (u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0))=u1_struct_0(esk6_0)|~r1_tarski(u1_struct_0(esk6_0),u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.21/0.49  cnf(c_0_67, negated_conjecture, (r1_tarski(u1_struct_0(esk6_0),u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)))), inference(spm,[status(thm)],[c_0_62, c_0_63])).
% 0.21/0.49  cnf(c_0_68, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.49  cnf(c_0_69, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_42]), c_0_30])])).
% 0.21/0.49  fof(c_0_70, plain, ![X10, X11, X12]:((r1_xboole_0(X10,k2_xboole_0(X11,X12))|~r1_xboole_0(X10,X11)|~r1_xboole_0(X10,X12))&((r1_xboole_0(X10,X11)|~r1_xboole_0(X10,k2_xboole_0(X11,X12)))&(r1_xboole_0(X10,X12)|~r1_xboole_0(X10,k2_xboole_0(X11,X12))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.21/0.49  cnf(c_0_71, negated_conjecture, (u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0))=u1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_66, c_0_67])])).
% 0.21/0.49  cnf(c_0_72, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))|~l1_struct_0(esk6_0)|~l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.21/0.49  cnf(c_0_73, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_70])).
% 0.21/0.49  cnf(c_0_74, negated_conjecture, (k2_xboole_0(u1_struct_0(esk6_0),u1_struct_0(esk5_0))=u1_struct_0(esk6_0)), inference(rw,[status(thm)],[c_0_63, c_0_71])).
% 0.21/0.49  cnf(c_0_75, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))|~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_42]), c_0_30])])).
% 0.21/0.49  cnf(c_0_76, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk5_0))|~r1_xboole_0(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.21/0.49  cnf(c_0_77, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_42]), c_0_59])])).
% 0.21/0.49  cnf(c_0_78, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.21/0.49  cnf(c_0_79, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.21/0.49  cnf(c_0_80, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_81, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.21/0.49  cnf(c_0_82, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_80]), c_0_22])])).
% 0.21/0.49  cnf(c_0_83, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)|~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_42]), c_0_82])])).
% 0.21/0.49  cnf(c_0_84, negated_conjecture, (~r1_tsep_1(esk5_0,esk7_0)|~r1_tsep_1(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.21/0.49  cnf(c_0_85, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_42]), c_0_59])])).
% 0.21/0.49  cnf(c_0_86, negated_conjecture, (~r1_tsep_1(esk5_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85])])).
% 0.21/0.49  cnf(c_0_87, negated_conjecture, (~l1_struct_0(esk5_0)|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_85]), c_0_86])).
% 0.21/0.49  cnf(c_0_88, negated_conjecture, (~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_42]), c_0_82])])).
% 0.21/0.49  cnf(c_0_89, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88, c_0_42]), c_0_59])]), ['proof']).
% 0.21/0.49  # SZS output end CNFRefutation
% 0.21/0.49  # Proof object total steps             : 90
% 0.21/0.49  # Proof object clause steps            : 63
% 0.21/0.49  # Proof object formula steps           : 27
% 0.21/0.49  # Proof object conjectures             : 44
% 0.21/0.49  # Proof object clause conjectures      : 41
% 0.21/0.49  # Proof object formula conjectures     : 3
% 0.21/0.49  # Proof object initial clauses used    : 26
% 0.21/0.49  # Proof object initial formulas used   : 13
% 0.21/0.49  # Proof object generating inferences   : 31
% 0.21/0.49  # Proof object simplifying inferences  : 55
% 0.21/0.49  # Training examples: 0 positive, 0 negative
% 0.21/0.49  # Parsed axioms                        : 13
% 0.21/0.49  # Removed by relevancy pruning/SinE    : 0
% 0.21/0.49  # Initial clauses                      : 42
% 0.21/0.49  # Removed in clause preprocessing      : 0
% 0.21/0.49  # Initial clauses in saturation        : 42
% 0.21/0.49  # Processed clauses                    : 980
% 0.21/0.49  # ...of these trivial                  : 22
% 0.21/0.49  # ...subsumed                          : 77
% 0.21/0.49  # ...remaining for further processing  : 881
% 0.21/0.49  # Other redundant clauses eliminated   : 4
% 0.21/0.49  # Clauses deleted for lack of memory   : 0
% 0.21/0.49  # Backward-subsumed                    : 9
% 0.21/0.49  # Backward-rewritten                   : 32
% 0.21/0.49  # Generated clauses                    : 5633
% 0.21/0.49  # ...of the previous two non-trivial   : 5227
% 0.21/0.49  # Contextual simplify-reflections      : 8
% 0.21/0.49  # Paramodulations                      : 5629
% 0.21/0.49  # Factorizations                       : 0
% 0.21/0.49  # Equation resolutions                 : 4
% 0.21/0.49  # Propositional unsat checks           : 0
% 0.21/0.49  #    Propositional check models        : 0
% 0.21/0.49  #    Propositional check unsatisfiable : 0
% 0.21/0.49  #    Propositional clauses             : 0
% 0.21/0.49  #    Propositional clauses after purity: 0
% 0.21/0.49  #    Propositional unsat core size     : 0
% 0.21/0.49  #    Propositional preprocessing time  : 0.000
% 0.21/0.49  #    Propositional encoding time       : 0.000
% 0.21/0.49  #    Propositional solver time         : 0.000
% 0.21/0.49  #    Success case prop preproc time    : 0.000
% 0.21/0.49  #    Success case prop encoding time   : 0.000
% 0.21/0.49  #    Success case prop solver time     : 0.000
% 0.21/0.49  # Current number of processed clauses  : 836
% 0.21/0.49  #    Positive orientable unit clauses  : 193
% 0.21/0.49  #    Positive unorientable unit clauses: 0
% 0.21/0.49  #    Negative unit clauses             : 6
% 0.21/0.49  #    Non-unit-clauses                  : 637
% 0.21/0.49  # Current number of unprocessed clauses: 4275
% 0.21/0.49  # ...number of literals in the above   : 15325
% 0.21/0.49  # Current number of archived formulas  : 0
% 0.21/0.49  # Current number of archived clauses   : 41
% 0.21/0.49  # Clause-clause subsumption calls (NU) : 11677
% 0.21/0.49  # Rec. Clause-clause subsumption calls : 8593
% 0.21/0.49  # Non-unit clause-clause subsumptions  : 94
% 0.21/0.49  # Unit Clause-clause subsumption calls : 4378
% 0.21/0.49  # Rewrite failures with RHS unbound    : 0
% 0.21/0.49  # BW rewrite match attempts            : 426
% 0.21/0.49  # BW rewrite match successes           : 25
% 0.21/0.49  # Condensation attempts                : 980
% 0.21/0.49  # Condensation successes               : 0
% 0.21/0.49  # Termbank termtop insertions          : 177206
% 0.21/0.49  
% 0.21/0.49  # -------------------------------------------------
% 0.21/0.49  # User time                : 0.145 s
% 0.21/0.49  # System time              : 0.006 s
% 0.21/0.49  # Total time               : 0.151 s
% 0.21/0.49  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
