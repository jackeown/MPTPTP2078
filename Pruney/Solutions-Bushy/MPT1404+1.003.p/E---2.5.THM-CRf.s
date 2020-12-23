%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1404+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:14 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 463 expanded)
%              Number of clauses        :   53 ( 168 expanded)
%              Number of leaves         :   14 ( 115 expanded)
%              Depth                    :   17
%              Number of atoms          :  443 (3557 expanded)
%              Number of equality atoms :   27 ( 132 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   76 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(dt_k1_tops_1,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(existence_m1_connsp_2,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ? [X3] : m1_connsp_2(X3,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(t34_connsp_2,conjecture,(
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
                    ( m1_connsp_2(X4,X1,X3)
                   => ~ r1_xboole_0(X4,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_connsp_2)).

fof(t5_connsp_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v3_pre_topc(X2,X1)
                  & r2_hidden(X3,X2) )
               => m1_connsp_2(X2,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

fof(d13_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k2_pre_topc(X1,X2)
              <=> ! [X4] :
                    ( r2_hidden(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ! [X5] :
                          ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
                         => ~ ( v3_pre_topc(X5,X1)
                              & r2_hidden(X4,X5)
                              & r1_xboole_0(X2,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_pre_topc)).

fof(symmetry_r1_xboole_0,axiom,(
    ! [X1,X2] :
      ( r1_xboole_0(X1,X2)
     => r1_xboole_0(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(dt_k2_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(t63_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_xboole_0(X2,X3) )
     => r1_xboole_0(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(t44_tops_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => r1_tarski(k1_tops_1(X1,X2),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(fc9_tops_1,axiom,(
    ! [X1,X2] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => v3_pre_topc(k1_tops_1(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(c_0_14,plain,(
    ! [X15,X16,X17] :
      ( ( ~ m1_connsp_2(X17,X15,X16)
        | r2_hidden(X16,k1_tops_1(X15,X17))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(X16,k1_tops_1(X15,X17))
        | m1_connsp_2(X17,X15,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_subset_1(X16,u1_struct_0(X15))
        | v2_struct_0(X15)
        | ~ v2_pre_topc(X15)
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_connsp_2])])])])])).

fof(c_0_15,plain,(
    ! [X22,X23,X24] :
      ( v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ m1_subset_1(X23,u1_struct_0(X22))
      | ~ m1_connsp_2(X24,X22,X23)
      | m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_m1_connsp_2])])])])).

fof(c_0_16,plain,(
    ! [X41,X42,X43] :
      ( ~ r2_hidden(X41,X42)
      | ~ m1_subset_1(X42,k1_zfmisc_1(X43))
      | ~ v1_xboole_0(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_17,plain,(
    ! [X18,X19] :
      ( ~ l1_pre_topc(X18)
      | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
      | m1_subset_1(k1_tops_1(X18,X19),k1_zfmisc_1(u1_struct_0(X18))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_tops_1])])).

cnf(c_0_18,plain,
    ( r2_hidden(X3,k1_tops_1(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_connsp_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_connsp_2(X3,X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X25,X26] :
      ( v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | ~ m1_subset_1(X26,u1_struct_0(X25))
      | m1_connsp_2(esk4_2(X25,X26),X25,X26) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[existence_m1_connsp_2])])])])).

fof(c_0_21,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_hidden(X3,k2_pre_topc(X1,X2))
                <=> ! [X4] :
                      ( m1_connsp_2(X4,X1,X3)
                     => ~ r1_xboole_0(X4,X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t34_connsp_2])).

fof(c_0_22,plain,(
    ! [X38,X39,X40] :
      ( v2_struct_0(X38)
      | ~ v2_pre_topc(X38)
      | ~ l1_pre_topc(X38)
      | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
      | ~ m1_subset_1(X40,u1_struct_0(X38))
      | ~ v3_pre_topc(X39,X38)
      | ~ r2_hidden(X40,X39)
      | m1_connsp_2(X39,X38,X40) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t5_connsp_2])])])])).

fof(c_0_23,plain,(
    ! [X6,X7,X8,X9,X10,X14] :
      ( ( ~ r2_hidden(X9,X8)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_pre_topc(X10,X6)
        | ~ r2_hidden(X9,X10)
        | ~ r1_xboole_0(X7,X10)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk1_4(X6,X7,X8,X9),k1_zfmisc_1(u1_struct_0(X6)))
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( v3_pre_topc(esk1_4(X6,X7,X8,X9),X6)
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(X9,esk1_4(X6,X7,X8,X9))
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r1_xboole_0(X7,esk1_4(X6,X7,X8,X9))
        | r2_hidden(X9,X8)
        | ~ r2_hidden(X9,u1_struct_0(X6))
        | X8 != k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),u1_struct_0(X6))
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( m1_subset_1(esk3_3(X6,X7,X8),k1_zfmisc_1(u1_struct_0(X6)))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( v3_pre_topc(esk3_3(X6,X7,X8),X6)
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),esk3_3(X6,X7,X8))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r1_xboole_0(X7,esk3_3(X6,X7,X8))
        | ~ r2_hidden(esk2_3(X6,X7,X8),X8)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) )
      & ( r2_hidden(esk2_3(X6,X7,X8),X8)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ v3_pre_topc(X14,X6)
        | ~ r2_hidden(esk2_3(X6,X7,X8),X14)
        | ~ r1_xboole_0(X7,X14)
        | X8 = k2_pre_topc(X6,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
        | ~ l1_pre_topc(X6) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d13_pre_topc])])])])])).

cnf(c_0_24,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( m1_subset_1(k1_tops_1(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_connsp_2(X3,X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(esk4_2(X1,X2),X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_28,negated_conjecture,(
    ! [X53] :
      ( ~ v2_struct_0(esk6_0)
      & v2_pre_topc(esk6_0)
      & l1_pre_topc(esk6_0)
      & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
      & m1_subset_1(esk8_0,u1_struct_0(esk6_0))
      & ( m1_connsp_2(esk9_0,esk6_0,esk8_0)
        | ~ r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0)) )
      & ( r1_xboole_0(esk9_0,esk7_0)
        | ~ r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0)) )
      & ( r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0))
        | ~ m1_connsp_2(X53,esk6_0,esk8_0)
        | ~ r1_xboole_0(X53,esk7_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_21])])])])])])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | m1_connsp_2(X2,X1,X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v3_pre_topc(X2,X1)
    | ~ r2_hidden(X3,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( v3_pre_topc(esk1_4(X1,X2,X3,X4),X1)
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_31,plain,
    ( m1_subset_1(esk1_4(X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X1)))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | X3 != k2_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_32,plain,(
    ! [X32,X33] :
      ( ~ r1_xboole_0(X32,X33)
      | r1_xboole_0(X33,X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_xboole_0])])).

fof(c_0_33,plain,(
    ! [X34,X35] :
      ( ~ m1_subset_1(X34,X35)
      | v1_xboole_0(X35)
      | r2_hidden(X34,X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(u1_struct_0(X1))
    | ~ r2_hidden(X2,k1_tops_1(X1,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,k1_tops_1(X1,esk4_2(X1,X2)))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_26,c_0_27])).

cnf(c_0_36,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk4_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_19,c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0))
    | ~ m1_connsp_2(X1,esk6_0,esk8_0)
    | ~ r1_xboole_0(X1,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,plain,
    ( m1_connsp_2(esk1_4(X1,X2,X3,X4),X1,X5)
    | v2_struct_0(X1)
    | r2_hidden(X4,X3)
    | X3 != k2_pre_topc(X1,X2)
    | ~ v2_pre_topc(X1)
    | ~ r2_hidden(X5,esk1_4(X1,X2,X3,X4))
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X5,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

cnf(c_0_39,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk6_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_41,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_43,plain,
    ( r1_xboole_0(X2,X1)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_44,plain,
    ( r1_xboole_0(X1,esk1_4(X2,X1,X3,X4))
    | r2_hidden(X4,X3)
    | ~ r2_hidden(X4,u1_struct_0(X2))
    | X3 != k2_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_45,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_46,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ v2_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0))
    | r2_hidden(X1,X2)
    | X2 != k2_pre_topc(esk6_0,X3)
    | ~ r1_xboole_0(esk1_4(esk6_0,X3,X2,X1),esk7_0)
    | ~ r2_hidden(esk8_0,esk1_4(esk6_0,X3,X2,X1))
    | ~ r2_hidden(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_48,plain,
    ( r1_xboole_0(esk1_4(X1,X2,X3,X4),X2)
    | r2_hidden(X4,X3)
    | X3 != k2_pre_topc(X1,X2)
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_50,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0))
    | r2_hidden(esk8_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_40])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_40]),c_0_39]),c_0_41])]),c_0_42])).

fof(c_0_52,plain,(
    ! [X20,X21] :
      ( ~ l1_pre_topc(X20)
      | ~ m1_subset_1(X21,k1_zfmisc_1(u1_struct_0(X20)))
      | m1_subset_1(k2_pre_topc(X20,X21),k1_zfmisc_1(u1_struct_0(X20))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_pre_topc])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0))
    | r2_hidden(X1,X2)
    | X2 != k2_pre_topc(esk6_0,esk7_0)
    | ~ r2_hidden(esk8_0,esk1_4(esk6_0,esk7_0,X2,X1))
    | ~ r2_hidden(X1,u1_struct_0(esk6_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_41])])).

cnf(c_0_54,plain,
    ( r2_hidden(X1,esk1_4(X2,X3,X4,X1))
    | r2_hidden(X1,X4)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | X4 != k2_pre_topc(X2,X3)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_56,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ v3_pre_topc(X3,X4)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X5,X3)
    | ~ r2_hidden(X1,u1_struct_0(X4))
    | X2 != k2_pre_topc(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_57,plain,
    ( m1_subset_1(k2_pre_topc(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0))
    | r2_hidden(esk8_0,X1)
    | X1 != k2_pre_topc(esk6_0,esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_49]),c_0_41])])).

cnf(c_0_59,plain,
    ( k2_pre_topc(X1,X2) != k2_pre_topc(X1,X3)
    | ~ r1_xboole_0(X3,X4)
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(X5,k2_pre_topc(X1,X2))
    | ~ r2_hidden(X5,u1_struct_0(X1))
    | ~ r2_hidden(X5,X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0))
    | ~ m1_subset_1(k2_pre_topc(esk6_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(er,[status(thm)],[c_0_58])).

fof(c_0_61,plain,(
    ! [X44,X45,X46] :
      ( ~ r1_tarski(X44,X45)
      | ~ r1_xboole_0(X45,X46)
      | r1_xboole_0(X44,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_xboole_1])])).

fof(c_0_62,plain,(
    ! [X36,X37] :
      ( ~ l1_pre_topc(X36)
      | ~ m1_subset_1(X37,k1_zfmisc_1(u1_struct_0(X36)))
      | r1_tarski(k1_tops_1(X36,X37),X37) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t44_tops_1])])])).

cnf(c_0_63,negated_conjecture,
    ( k2_pre_topc(esk6_0,esk7_0) != k2_pre_topc(esk6_0,X1)
    | ~ r1_xboole_0(X1,X2)
    | ~ v3_pre_topc(X2,esk6_0)
    | ~ r2_hidden(esk8_0,X2)
    | ~ m1_subset_1(k2_pre_topc(esk6_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_55]),c_0_49]),c_0_41])])).

fof(c_0_64,plain,(
    ! [X30,X31] :
      ( ~ v2_pre_topc(X30)
      | ~ l1_pre_topc(X30)
      | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
      | v3_pre_topc(k1_tops_1(X30,X31),X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc9_tops_1])])).

cnf(c_0_65,plain,
    ( r1_xboole_0(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_66,plain,
    ( r1_tarski(k1_tops_1(X1,X2),X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_67,negated_conjecture,
    ( k2_pre_topc(esk6_0,esk7_0) != k2_pre_topc(esk6_0,X1)
    | ~ r1_xboole_0(X1,X2)
    | ~ v3_pre_topc(X2,esk6_0)
    | ~ r2_hidden(esk8_0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_57]),c_0_49]),c_0_41])])).

cnf(c_0_68,plain,
    ( v3_pre_topc(k1_tops_1(X1,X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_69,negated_conjecture,
    ( m1_connsp_2(esk9_0,esk6_0,esk8_0)
    | ~ r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_70,plain,
    ( r1_xboole_0(k1_tops_1(X1,X2),X3)
    | ~ r1_xboole_0(X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( k2_pre_topc(esk6_0,esk7_0) != k2_pre_topc(esk6_0,X1)
    | ~ r1_xboole_0(X1,k1_tops_1(esk6_0,X2))
    | ~ r2_hidden(esk8_0,k1_tops_1(esk6_0,X2))
    | ~ m1_subset_1(k1_tops_1(esk6_0,X2),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_39]),c_0_41])])).

cnf(c_0_72,negated_conjecture,
    ( r2_hidden(esk8_0,k1_tops_1(esk6_0,esk9_0))
    | ~ r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_69]),c_0_39]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_69]),c_0_39]),c_0_40]),c_0_41])]),c_0_42])).

cnf(c_0_74,plain,
    ( r1_xboole_0(X1,k1_tops_1(X2,X3))
    | ~ r1_xboole_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_43,c_0_70])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(esk9_0,esk7_0)
    | ~ r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_76,negated_conjecture,
    ( k2_pre_topc(esk6_0,esk7_0) != k2_pre_topc(esk6_0,X1)
    | ~ r1_xboole_0(X1,k1_tops_1(esk6_0,esk9_0))
    | ~ r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0))
    | ~ m1_subset_1(k1_tops_1(esk6_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(esk7_0,k1_tops_1(X1,esk9_0))
    | ~ r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0))
    | ~ m1_subset_1(esk9_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0))
    | ~ m1_subset_1(k1_tops_1(esk6_0,esk9_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_49]),c_0_41])]),c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( ~ r2_hidden(esk8_0,k2_pre_topc(esk6_0,esk7_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_25]),c_0_41])]),c_0_73])).

cnf(c_0_80,negated_conjecture,
    ( ~ m1_subset_1(k2_pre_topc(esk6_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(spm,[status(thm)],[c_0_79,c_0_60])).

cnf(c_0_81,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_57]),c_0_49]),c_0_41])]),
    [proof]).

%------------------------------------------------------------------------------
