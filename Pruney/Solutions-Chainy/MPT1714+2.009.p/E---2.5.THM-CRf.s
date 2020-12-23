%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:58 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 893 expanded)
%              Number of clauses        :   61 ( 338 expanded)
%              Number of leaves         :   13 ( 220 expanded)
%              Depth                    :   20
%              Number of atoms          :  396 (6947 expanded)
%              Number of equality atoms :   29 ( 126 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

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

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(t7_xboole_1,axiom,(
    ! [X1,X2] : r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(d3_tsep_1,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ( r1_tsep_1(X1,X2)
          <=> r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(t70_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ~ ( ~ r1_xboole_0(X1,k2_xboole_0(X2,X3))
          & r1_xboole_0(X1,X2)
          & r1_xboole_0(X1,X3) )
      & ~ ( ~ ( r1_xboole_0(X1,X2)
              & r1_xboole_0(X1,X3) )
          & r1_xboole_0(X1,k2_xboole_0(X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

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
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
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
    ! [X35,X36,X37] :
      ( ( ~ r1_tarski(u1_struct_0(X36),u1_struct_0(X37))
        | m1_pre_topc(X36,X37)
        | ~ m1_pre_topc(X37,X35)
        | ~ m1_pre_topc(X36,X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) )
      & ( ~ m1_pre_topc(X36,X37)
        | r1_tarski(u1_struct_0(X36),u1_struct_0(X37))
        | ~ m1_pre_topc(X37,X35)
        | ~ m1_pre_topc(X36,X35)
        | ~ v2_pre_topc(X35)
        | ~ l1_pre_topc(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_18,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_19,plain,(
    ! [X30,X31,X32] :
      ( ( ~ v2_struct_0(k1_tsep_1(X30,X31,X32))
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30) )
      & ( v1_pre_topc(k1_tsep_1(X30,X31,X32))
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30) )
      & ( m1_pre_topc(k1_tsep_1(X30,X31,X32),X30)
        | v2_struct_0(X30)
        | ~ l1_pre_topc(X30)
        | v2_struct_0(X31)
        | ~ m1_pre_topc(X31,X30)
        | v2_struct_0(X32)
        | ~ m1_pre_topc(X32,X30) ) ) ),
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
    ! [X13,X14,X15,X17,X19] :
      ( ( r1_tarski(k2_struct_0(X14),k2_struct_0(X13))
        | ~ m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(X15,u1_pre_topc(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk1_3(X13,X14,X15),u1_pre_topc(X13))
        | ~ r2_hidden(X15,u1_pre_topc(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( X15 = k9_subset_1(u1_struct_0(X14),esk1_3(X13,X14,X15),k2_struct_0(X14))
        | ~ r2_hidden(X15,u1_pre_topc(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(X17,u1_pre_topc(X13))
        | X15 != k9_subset_1(u1_struct_0(X14),X17,k2_struct_0(X14))
        | r2_hidden(X15,u1_pre_topc(X14))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk2_2(X13,X14),k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r1_tarski(k2_struct_0(X14),k2_struct_0(X13))
        | m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( ~ r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ r2_hidden(X19,u1_pre_topc(X13))
        | esk2_2(X13,X14) != k9_subset_1(u1_struct_0(X14),X19,k2_struct_0(X14))
        | ~ r1_tarski(k2_struct_0(X14),k2_struct_0(X13))
        | m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( m1_subset_1(esk3_2(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))
        | r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))
        | ~ r1_tarski(k2_struct_0(X14),k2_struct_0(X13))
        | m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( r2_hidden(esk3_2(X13,X14),u1_pre_topc(X13))
        | r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))
        | ~ r1_tarski(k2_struct_0(X14),k2_struct_0(X13))
        | m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) )
      & ( esk2_2(X13,X14) = k9_subset_1(u1_struct_0(X14),esk3_2(X13,X14),k2_struct_0(X14))
        | r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))
        | ~ r1_tarski(k2_struct_0(X14),k2_struct_0(X13))
        | m1_pre_topc(X14,X13)
        | ~ l1_pre_topc(X14)
        | ~ l1_pre_topc(X13) ) ) ),
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

fof(c_0_33,plain,(
    ! [X24,X25,X26,X27] :
      ( ( X27 != k1_tsep_1(X24,X25,X26)
        | u1_struct_0(X27) = k2_xboole_0(u1_struct_0(X25),u1_struct_0(X26))
        | v2_struct_0(X27)
        | ~ v1_pre_topc(X27)
        | ~ m1_pre_topc(X27,X24)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ l1_pre_topc(X24) )
      & ( u1_struct_0(X27) != k2_xboole_0(u1_struct_0(X25),u1_struct_0(X26))
        | X27 = k1_tsep_1(X24,X25,X26)
        | v2_struct_0(X27)
        | ~ v1_pre_topc(X27)
        | ~ m1_pre_topc(X27,X24)
        | v2_struct_0(X26)
        | ~ m1_pre_topc(X26,X24)
        | v2_struct_0(X25)
        | ~ m1_pre_topc(X25,X24)
        | v2_struct_0(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).

cnf(c_0_34,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_35,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk6_0,X1,esk5_0),esk6_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28]),c_0_29]),c_0_30])])).

cnf(c_0_36,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_21]),c_0_32]),c_0_22])])).

fof(c_0_37,plain,(
    ! [X12] :
      ( ~ l1_struct_0(X12)
      | k2_struct_0(X12) = u1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_38,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_39,plain,(
    ! [X33,X34] :
      ( ~ l1_struct_0(X33)
      | ~ l1_struct_0(X34)
      | ~ r1_tsep_1(X33,X34)
      | r1_tsep_1(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_40,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_43,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_34,c_0_20])).

cnf(c_0_44,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_28])).

cnf(c_0_45,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r1_tsep_1(esk6_0,esk7_0)
    | r1_tsep_1(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_49,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_50,plain,(
    ! [X10,X11] : r1_tarski(X10,k2_xboole_0(X10,X11)) ),
    inference(variable_rename,[status(thm)],[t7_xboole_1])).

cnf(c_0_51,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_26]),c_0_41]),c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),k2_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_30])])).

cnf(c_0_53,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0)
    | ~ l1_struct_0(esk7_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_49]),c_0_22])])).

cnf(c_0_56,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_57,plain,
    ( r1_tarski(X1,k2_xboole_0(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk5_0)) = u1_struct_0(k1_tsep_1(esk6_0,X1,esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_27]),c_0_30])]),c_0_29]),c_0_28])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_53]),c_0_30])])).

cnf(c_0_60,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_44]),c_0_30])])).

fof(c_0_61,plain,(
    ! [X28,X29] :
      ( ( ~ r1_tsep_1(X28,X29)
        | r1_xboole_0(u1_struct_0(X28),u1_struct_0(X29))
        | ~ l1_struct_0(X29)
        | ~ l1_struct_0(X28) )
      & ( ~ r1_xboole_0(u1_struct_0(X28),u1_struct_0(X29))
        | r1_tsep_1(X28,X29)
        | ~ l1_struct_0(X29)
        | ~ l1_struct_0(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).

cnf(c_0_62,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_46]),c_0_55])])).

cnf(c_0_63,plain,
    ( k2_xboole_0(X1,X2) = X1
    | ~ r1_tarski(k2_xboole_0(X1,X2),X1) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk6_0),u1_struct_0(esk5_0)) = u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_36]),c_0_28])).

cnf(c_0_65,negated_conjecture,
    ( r1_tarski(u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_53]),c_0_60])])).

cnf(c_0_66,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_46]),c_0_30])])).

fof(c_0_68,plain,(
    ! [X7,X8,X9] :
      ( ( r1_xboole_0(X7,k2_xboole_0(X8,X9))
        | ~ r1_xboole_0(X7,X8)
        | ~ r1_xboole_0(X7,X9) )
      & ( r1_xboole_0(X7,X8)
        | ~ r1_xboole_0(X7,k2_xboole_0(X8,X9)) )
      & ( r1_xboole_0(X7,X9)
        | ~ r1_xboole_0(X7,k2_xboole_0(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_69,negated_conjecture,
    ( u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)) = u1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65])])).

cnf(c_0_70,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk6_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_66,c_0_67])).

cnf(c_0_71,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_72,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk6_0),u1_struct_0(esk5_0)) = u1_struct_0(esk6_0) ),
    inference(rw,[status(thm)],[c_0_64,c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_46]),c_0_30])])).

cnf(c_0_74,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk5_0))
    | ~ r1_xboole_0(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_46]),c_0_55])])).

cnf(c_0_76,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_77,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_79,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_78]),c_0_22])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_46]),c_0_80])])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk7_0)
    | ~ r1_tsep_1(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_83,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_46]),c_0_55])])).

cnf(c_0_84,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83])])).

cnf(c_0_85,negated_conjecture,
    ( ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_83]),c_0_84])).

cnf(c_0_86,negated_conjecture,
    ( ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_46]),c_0_80])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_46]),c_0_55])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.50  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.20/0.50  # and selection function SelectNewComplexAHPNS.
% 0.20/0.50  #
% 0.20/0.50  # Preprocessing time       : 0.028 s
% 0.20/0.50  
% 0.20/0.50  # Proof found!
% 0.20/0.50  # SZS status Theorem
% 0.20/0.50  # SZS output start CNFRefutation
% 0.20/0.50  fof(t23_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_tmap_1)).
% 0.20/0.50  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.50  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.50  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.20/0.50  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.20/0.50  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.20/0.50  fof(d2_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k1_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tsep_1)).
% 0.20/0.50  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 0.20/0.50  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.50  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.20/0.50  fof(t7_xboole_1, axiom, ![X1, X2]:r1_tarski(X1,k2_xboole_0(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 0.20/0.50  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.20/0.50  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.20/0.50  fof(c_0_13, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))))))))), inference(assume_negation,[status(cth)],[t23_tmap_1])).
% 0.20/0.50  fof(c_0_14, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.50  fof(c_0_15, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|l1_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.50  fof(c_0_16, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk4_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk4_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk4_0))&(m1_pre_topc(esk5_0,esk6_0)&((~r1_tsep_1(esk5_0,esk7_0)|~r1_tsep_1(esk7_0,esk5_0))&(r1_tsep_1(esk6_0,esk7_0)|r1_tsep_1(esk7_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).
% 0.20/0.50  fof(c_0_17, plain, ![X35, X36, X37]:((~r1_tarski(u1_struct_0(X36),u1_struct_0(X37))|m1_pre_topc(X36,X37)|~m1_pre_topc(X37,X35)|~m1_pre_topc(X36,X35)|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))&(~m1_pre_topc(X36,X37)|r1_tarski(u1_struct_0(X36),u1_struct_0(X37))|~m1_pre_topc(X37,X35)|~m1_pre_topc(X36,X35)|(~v2_pre_topc(X35)|~l1_pre_topc(X35)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.20/0.50  cnf(c_0_18, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  fof(c_0_19, plain, ![X30, X31, X32]:(((~v2_struct_0(k1_tsep_1(X30,X31,X32))|(v2_struct_0(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~m1_pre_topc(X31,X30)|v2_struct_0(X32)|~m1_pre_topc(X32,X30)))&(v1_pre_topc(k1_tsep_1(X30,X31,X32))|(v2_struct_0(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~m1_pre_topc(X31,X30)|v2_struct_0(X32)|~m1_pre_topc(X32,X30))))&(m1_pre_topc(k1_tsep_1(X30,X31,X32),X30)|(v2_struct_0(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~m1_pre_topc(X31,X30)|v2_struct_0(X32)|~m1_pre_topc(X32,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.20/0.50  cnf(c_0_20, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.50  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_23, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.50  cnf(c_0_24, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_18])).
% 0.20/0.50  fof(c_0_25, plain, ![X13, X14, X15, X17, X19]:(((r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|~m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))&((((m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X13)))|~r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))&(r2_hidden(esk1_3(X13,X14,X15),u1_pre_topc(X13))|~r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13)))&(X15=k9_subset_1(u1_struct_0(X14),esk1_3(X13,X14,X15),k2_struct_0(X14))|~r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13)))&(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X13)))|~r2_hidden(X17,u1_pre_topc(X13))|X15!=k9_subset_1(u1_struct_0(X14),X17,k2_struct_0(X14))|r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))))&((m1_subset_1(esk2_2(X13,X14),k1_zfmisc_1(u1_struct_0(X14)))|~r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))&((~r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X13)))|~r2_hidden(X19,u1_pre_topc(X13))|esk2_2(X13,X14)!=k9_subset_1(u1_struct_0(X14),X19,k2_struct_0(X14)))|~r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))&(((m1_subset_1(esk3_2(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))|r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))|~r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))&(r2_hidden(esk3_2(X13,X14),u1_pre_topc(X13))|r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))|~r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13)))&(esk2_2(X13,X14)=k9_subset_1(u1_struct_0(X14),esk3_2(X13,X14),k2_struct_0(X14))|r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))|~r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.20/0.50  cnf(c_0_26, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.50  cnf(c_0_27, negated_conjecture, (m1_pre_topc(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_28, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_29, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.20/0.50  cnf(c_0_31, plain, (m1_pre_topc(X1,X1)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.50  cnf(c_0_32, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  fof(c_0_33, plain, ![X24, X25, X26, X27]:((X27!=k1_tsep_1(X24,X25,X26)|u1_struct_0(X27)=k2_xboole_0(u1_struct_0(X25),u1_struct_0(X26))|(v2_struct_0(X27)|~v1_pre_topc(X27)|~m1_pre_topc(X27,X24))|(v2_struct_0(X26)|~m1_pre_topc(X26,X24))|(v2_struct_0(X25)|~m1_pre_topc(X25,X24))|(v2_struct_0(X24)|~l1_pre_topc(X24)))&(u1_struct_0(X27)!=k2_xboole_0(u1_struct_0(X25),u1_struct_0(X26))|X27=k1_tsep_1(X24,X25,X26)|(v2_struct_0(X27)|~v1_pre_topc(X27)|~m1_pre_topc(X27,X24))|(v2_struct_0(X26)|~m1_pre_topc(X26,X24))|(v2_struct_0(X25)|~m1_pre_topc(X25,X24))|(v2_struct_0(X24)|~l1_pre_topc(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).
% 0.20/0.50  cnf(c_0_34, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.50  cnf(c_0_35, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk6_0,X1,esk5_0),esk6_0)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_28]), c_0_29]), c_0_30])])).
% 0.20/0.50  cnf(c_0_36, negated_conjecture, (m1_pre_topc(esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_21]), c_0_32]), c_0_22])])).
% 0.20/0.50  fof(c_0_37, plain, ![X12]:(~l1_struct_0(X12)|k2_struct_0(X12)=u1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.20/0.50  fof(c_0_38, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.50  fof(c_0_39, plain, ![X33, X34]:(~l1_struct_0(X33)|~l1_struct_0(X34)|(~r1_tsep_1(X33,X34)|r1_tsep_1(X34,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.20/0.50  cnf(c_0_40, plain, (u1_struct_0(X1)=k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k1_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.50  cnf(c_0_41, plain, (v1_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.50  cnf(c_0_42, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.50  cnf(c_0_43, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_34, c_0_20])).
% 0.20/0.50  cnf(c_0_44, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_28])).
% 0.20/0.50  cnf(c_0_45, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.50  cnf(c_0_46, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_38])).
% 0.20/0.50  cnf(c_0_47, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.50  cnf(c_0_48, negated_conjecture, (r1_tsep_1(esk6_0,esk7_0)|r1_tsep_1(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_49, negated_conjecture, (m1_pre_topc(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  fof(c_0_50, plain, ![X10, X11]:r1_tarski(X10,k2_xboole_0(X10,X11)), inference(variable_rename,[status(thm)],[t7_xboole_1])).
% 0.20/0.50  cnf(c_0_51, plain, (u1_struct_0(k1_tsep_1(X1,X2,X3))=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]), c_0_26]), c_0_41]), c_0_42])).
% 0.20/0.50  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),k2_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_44]), c_0_30])])).
% 0.20/0.50  cnf(c_0_53, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_45, c_0_46])).
% 0.20/0.50  cnf(c_0_54, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)|~l1_struct_0(esk7_0)|~l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_47, c_0_48])).
% 0.20/0.50  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_49]), c_0_22])])).
% 0.20/0.50  cnf(c_0_56, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.50  cnf(c_0_57, plain, (r1_tarski(X1,k2_xboole_0(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.50  cnf(c_0_58, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk5_0))=u1_struct_0(k1_tsep_1(esk6_0,X1,esk5_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_27]), c_0_30])]), c_0_29]), c_0_28])).
% 0.20/0.50  cnf(c_0_59, negated_conjecture, (r1_tarski(k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_53]), c_0_30])])).
% 0.20/0.50  cnf(c_0_60, negated_conjecture, (l1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_44]), c_0_30])])).
% 0.20/0.50  fof(c_0_61, plain, ![X28, X29]:((~r1_tsep_1(X28,X29)|r1_xboole_0(u1_struct_0(X28),u1_struct_0(X29))|~l1_struct_0(X29)|~l1_struct_0(X28))&(~r1_xboole_0(u1_struct_0(X28),u1_struct_0(X29))|r1_tsep_1(X28,X29)|~l1_struct_0(X29)|~l1_struct_0(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.20/0.50  cnf(c_0_62, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)|~l1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_46]), c_0_55])])).
% 0.20/0.50  cnf(c_0_63, plain, (k2_xboole_0(X1,X2)=X1|~r1_tarski(k2_xboole_0(X1,X2),X1)), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.20/0.50  cnf(c_0_64, negated_conjecture, (k2_xboole_0(u1_struct_0(esk6_0),u1_struct_0(esk5_0))=u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_36]), c_0_28])).
% 0.20/0.50  cnf(c_0_65, negated_conjecture, (r1_tarski(u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_53]), c_0_60])])).
% 0.20/0.50  cnf(c_0_66, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.50  cnf(c_0_67, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_46]), c_0_30])])).
% 0.20/0.50  fof(c_0_68, plain, ![X7, X8, X9]:((r1_xboole_0(X7,k2_xboole_0(X8,X9))|~r1_xboole_0(X7,X8)|~r1_xboole_0(X7,X9))&((r1_xboole_0(X7,X8)|~r1_xboole_0(X7,k2_xboole_0(X8,X9)))&(r1_xboole_0(X7,X9)|~r1_xboole_0(X7,k2_xboole_0(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.20/0.50  cnf(c_0_69, negated_conjecture, (u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0))=u1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_65])])).
% 0.20/0.50  cnf(c_0_70, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))|~l1_struct_0(esk6_0)|~l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_66, c_0_67])).
% 0.20/0.50  cnf(c_0_71, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_68])).
% 0.20/0.50  cnf(c_0_72, negated_conjecture, (k2_xboole_0(u1_struct_0(esk6_0),u1_struct_0(esk5_0))=u1_struct_0(esk6_0)), inference(rw,[status(thm)],[c_0_64, c_0_69])).
% 0.20/0.50  cnf(c_0_73, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))|~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_46]), c_0_30])])).
% 0.20/0.50  cnf(c_0_74, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk5_0))|~r1_xboole_0(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_71, c_0_72])).
% 0.20/0.50  cnf(c_0_75, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_46]), c_0_55])])).
% 0.20/0.50  cnf(c_0_76, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.20/0.50  cnf(c_0_77, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.20/0.50  cnf(c_0_78, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_79, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_76, c_0_77])).
% 0.20/0.50  cnf(c_0_80, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_78]), c_0_22])])).
% 0.20/0.50  cnf(c_0_81, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)|~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_46]), c_0_80])])).
% 0.20/0.50  cnf(c_0_82, negated_conjecture, (~r1_tsep_1(esk5_0,esk7_0)|~r1_tsep_1(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.50  cnf(c_0_83, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_46]), c_0_55])])).
% 0.20/0.50  cnf(c_0_84, negated_conjecture, (~r1_tsep_1(esk5_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83])])).
% 0.20/0.50  cnf(c_0_85, negated_conjecture, (~l1_struct_0(esk5_0)|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_83]), c_0_84])).
% 0.20/0.50  cnf(c_0_86, negated_conjecture, (~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85, c_0_46]), c_0_80])])).
% 0.20/0.50  cnf(c_0_87, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_46]), c_0_55])]), ['proof']).
% 0.20/0.50  # SZS output end CNFRefutation
% 0.20/0.50  # Proof object total steps             : 88
% 0.20/0.50  # Proof object clause steps            : 61
% 0.20/0.50  # Proof object formula steps           : 27
% 0.20/0.50  # Proof object conjectures             : 42
% 0.20/0.50  # Proof object clause conjectures      : 39
% 0.20/0.50  # Proof object formula conjectures     : 3
% 0.20/0.50  # Proof object initial clauses used    : 26
% 0.20/0.50  # Proof object initial formulas used   : 13
% 0.20/0.50  # Proof object generating inferences   : 30
% 0.20/0.50  # Proof object simplifying inferences  : 55
% 0.20/0.50  # Training examples: 0 positive, 0 negative
% 0.20/0.50  # Parsed axioms                        : 13
% 0.20/0.50  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.50  # Initial clauses                      : 42
% 0.20/0.50  # Removed in clause preprocessing      : 0
% 0.20/0.50  # Initial clauses in saturation        : 42
% 0.20/0.50  # Processed clauses                    : 1072
% 0.20/0.50  # ...of these trivial                  : 22
% 0.20/0.50  # ...subsumed                          : 109
% 0.20/0.50  # ...remaining for further processing  : 941
% 0.20/0.50  # Other redundant clauses eliminated   : 4
% 0.20/0.50  # Clauses deleted for lack of memory   : 0
% 0.20/0.50  # Backward-subsumed                    : 11
% 0.20/0.50  # Backward-rewritten                   : 33
% 0.20/0.50  # Generated clauses                    : 6019
% 0.20/0.50  # ...of the previous two non-trivial   : 5607
% 0.20/0.50  # Contextual simplify-reflections      : 8
% 0.20/0.50  # Paramodulations                      : 6015
% 0.20/0.50  # Factorizations                       : 0
% 0.20/0.50  # Equation resolutions                 : 4
% 0.20/0.50  # Propositional unsat checks           : 0
% 0.20/0.50  #    Propositional check models        : 0
% 0.20/0.50  #    Propositional check unsatisfiable : 0
% 0.20/0.50  #    Propositional clauses             : 0
% 0.20/0.50  #    Propositional clauses after purity: 0
% 0.20/0.50  #    Propositional unsat core size     : 0
% 0.20/0.50  #    Propositional preprocessing time  : 0.000
% 0.20/0.50  #    Propositional encoding time       : 0.000
% 0.20/0.50  #    Propositional solver time         : 0.000
% 0.20/0.50  #    Success case prop preproc time    : 0.000
% 0.20/0.50  #    Success case prop encoding time   : 0.000
% 0.20/0.50  #    Success case prop solver time     : 0.000
% 0.20/0.50  # Current number of processed clauses  : 893
% 0.20/0.50  #    Positive orientable unit clauses  : 195
% 0.20/0.50  #    Positive unorientable unit clauses: 0
% 0.20/0.50  #    Negative unit clauses             : 6
% 0.20/0.50  #    Non-unit-clauses                  : 692
% 0.20/0.50  # Current number of unprocessed clauses: 4565
% 0.20/0.50  # ...number of literals in the above   : 17005
% 0.20/0.50  # Current number of archived formulas  : 0
% 0.20/0.50  # Current number of archived clauses   : 44
% 0.20/0.50  # Clause-clause subsumption calls (NU) : 14042
% 0.20/0.50  # Rec. Clause-clause subsumption calls : 9860
% 0.20/0.50  # Non-unit clause-clause subsumptions  : 128
% 0.20/0.50  # Unit Clause-clause subsumption calls : 4432
% 0.20/0.50  # Rewrite failures with RHS unbound    : 0
% 0.20/0.50  # BW rewrite match attempts            : 415
% 0.20/0.50  # BW rewrite match successes           : 26
% 0.20/0.50  # Condensation attempts                : 1072
% 0.20/0.50  # Condensation successes               : 0
% 0.20/0.50  # Termbank termtop insertions          : 192816
% 0.20/0.50  
% 0.20/0.50  # -------------------------------------------------
% 0.20/0.50  # User time                : 0.144 s
% 0.20/0.50  # System time              : 0.009 s
% 0.20/0.50  # Total time               : 0.153 s
% 0.20/0.50  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
