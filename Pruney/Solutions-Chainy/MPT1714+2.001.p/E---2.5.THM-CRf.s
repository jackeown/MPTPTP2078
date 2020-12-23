%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:57 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 (3097 expanded)
%              Number of clauses        :   72 (1134 expanded)
%              Number of leaves         :   14 ( 754 expanded)
%              Depth                    :   23
%              Number of atoms          :  448 (25597 expanded)
%              Number of equality atoms :   30 ( 362 expanded)
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

fof(cc1_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => v2_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

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

fof(t22_tsep_1,axiom,(
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
             => m1_pre_topc(X2,k1_tsep_1(X1,X2,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

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

fof(symmetry_r1_tsep_1,axiom,(
    ! [X1,X2] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2) )
     => ( r1_tsep_1(X1,X2)
       => r1_tsep_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

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

fof(c_0_14,negated_conjecture,(
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

fof(c_0_15,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_16,plain,(
    ! [X22,X23] :
      ( ~ l1_pre_topc(X22)
      | ~ m1_pre_topc(X23,X22)
      | l1_pre_topc(X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_17,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).

fof(c_0_18,plain,(
    ! [X38,X39,X40] :
      ( ( ~ r1_tarski(u1_struct_0(X39),u1_struct_0(X40))
        | m1_pre_topc(X39,X40)
        | ~ m1_pre_topc(X40,X38)
        | ~ m1_pre_topc(X39,X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) )
      & ( ~ m1_pre_topc(X39,X40)
        | r1_tarski(u1_struct_0(X39),u1_struct_0(X40))
        | ~ m1_pre_topc(X40,X38)
        | ~ m1_pre_topc(X39,X38)
        | ~ v2_pre_topc(X38)
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).

cnf(c_0_19,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_20,plain,(
    ! [X10,X11] :
      ( ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ m1_pre_topc(X11,X10)
      | v2_pre_topc(X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).

fof(c_0_21,plain,(
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

cnf(c_0_22,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_25,plain,
    ( m1_pre_topc(X1,X2)
    | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_19])).

fof(c_0_27,plain,(
    ! [X35,X36,X37] :
      ( v2_struct_0(X35)
      | ~ v2_pre_topc(X35)
      | ~ l1_pre_topc(X35)
      | v2_struct_0(X36)
      | ~ m1_pre_topc(X36,X35)
      | v2_struct_0(X37)
      | ~ m1_pre_topc(X37,X35)
      | m1_pre_topc(X36,k1_tsep_1(X35,X36,X37)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).

cnf(c_0_28,plain,
    ( v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_29,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_30,plain,
    ( m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_34,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_35,plain,
    ( m1_pre_topc(X1,X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_36,plain,(
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

cnf(c_0_37,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_38,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_23]),c_0_24]),c_0_29])])).

cnf(c_0_39,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(k1_tsep_1(esk6_0,X1,esk5_0),esk6_0)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33]),c_0_34])])).

cnf(c_0_40,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_23]),c_0_24]),c_0_29])])).

cnf(c_0_41,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_42,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_pre_topc(X1,k1_tsep_1(esk6_0,X1,esk5_0))
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_31]),c_0_32]),c_0_33]),c_0_34]),c_0_38])])).

cnf(c_0_43,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0),esk6_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_32])).

fof(c_0_44,plain,(
    ! [X12] :
      ( ~ l1_struct_0(X12)
      | k2_struct_0(X12) = u1_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_45,plain,(
    ! [X21] :
      ( ~ l1_pre_topc(X21)
      | l1_struct_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_46,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_41,c_0_22])).

cnf(c_0_47,negated_conjecture,
    ( m1_pre_topc(esk6_0,k1_tsep_1(esk6_0,esk6_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_40]),c_0_32])).

cnf(c_0_48,negated_conjecture,
    ( l1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_43]),c_0_34])])).

cnf(c_0_49,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk6_0),k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_48])])).

cnf(c_0_53,negated_conjecture,
    ( r1_tarski(k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),k2_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_43]),c_0_34])])).

fof(c_0_54,plain,(
    ! [X33,X34] :
      ( ~ l1_struct_0(X33)
      | ~ l1_struct_0(X34)
      | ~ r1_tsep_1(X33,X34)
      | r1_tsep_1(X34,X33) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).

cnf(c_0_55,plain,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_pre_topc(X1,X3)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_56,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_57,negated_conjecture,
    ( k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)) = k2_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_52]),c_0_53])])).

cnf(c_0_58,plain,
    ( r1_tsep_1(X2,X1)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ r1_tsep_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_59,negated_conjecture,
    ( r1_tsep_1(esk6_0,esk7_0)
    | r1_tsep_1(esk7_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_60,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_61,plain,(
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

cnf(c_0_62,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),u1_struct_0(esk6_0))
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_40]),c_0_34]),c_0_38])])).

cnf(c_0_63,negated_conjecture,
    ( u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)) = k2_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_48])])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0),k1_tsep_1(esk6_0,esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_43]),c_0_34]),c_0_38])])).

cnf(c_0_65,negated_conjecture,
    ( v2_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_43]),c_0_34]),c_0_38])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0)
    | ~ l1_struct_0(esk7_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_60]),c_0_24])])).

cnf(c_0_68,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,plain,
    ( v1_pre_topc(k1_tsep_1(X1,X2,X3))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_70,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | ~ v2_struct_0(k1_tsep_1(X1,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_pre_topc(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(k2_struct_0(esk6_0),u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_43]),c_0_63])).

cnf(c_0_72,negated_conjecture,
    ( r1_tarski(u1_struct_0(X1),k2_struct_0(esk6_0))
    | ~ m1_pre_topc(X1,k1_tsep_1(esk6_0,esk6_0,esk5_0)) ),
    inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_64]),c_0_48]),c_0_65])]),c_0_63])).

fof(c_0_73,plain,(
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

cnf(c_0_74,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0)
    | ~ l1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_50]),c_0_67])])).

cnf(c_0_75,plain,
    ( u1_struct_0(k1_tsep_1(X1,X2,X3)) = k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_68]),c_0_30]),c_0_69]),c_0_70])).

cnf(c_0_76,negated_conjecture,
    ( k2_struct_0(esk6_0) = u1_struct_0(esk6_0)
    | ~ r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_72,c_0_47])).

cnf(c_0_78,plain,
    ( r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ r1_tsep_1(X1,X2)
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_79,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_50]),c_0_34])])).

fof(c_0_80,plain,(
    ! [X7,X8,X9] :
      ( ( r1_xboole_0(X7,k2_xboole_0(X8,X9))
        | ~ r1_xboole_0(X7,X8)
        | ~ r1_xboole_0(X7,X9) )
      & ( r1_xboole_0(X7,X8)
        | ~ r1_xboole_0(X7,k2_xboole_0(X8,X9)) )
      & ( r1_xboole_0(X7,X9)
        | ~ r1_xboole_0(X7,k2_xboole_0(X8,X9)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).

cnf(c_0_81,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk5_0)) = u1_struct_0(k1_tsep_1(esk6_0,X1,esk5_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk6_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_31]),c_0_34])]),c_0_33]),c_0_32])).

cnf(c_0_82,negated_conjecture,
    ( k2_struct_0(esk6_0) = u1_struct_0(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_77])])).

cnf(c_0_83,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk6_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_84,plain,
    ( r1_xboole_0(X1,X2)
    | ~ r1_xboole_0(X1,k2_xboole_0(X3,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_85,negated_conjecture,
    ( k2_xboole_0(u1_struct_0(esk6_0),u1_struct_0(esk5_0)) = u1_struct_0(esk6_0) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_40]),c_0_63]),c_0_82]),c_0_32])).

cnf(c_0_86,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))
    | ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_50]),c_0_34])])).

cnf(c_0_87,negated_conjecture,
    ( r1_xboole_0(X1,u1_struct_0(esk5_0))
    | ~ r1_xboole_0(X1,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_85])).

cnf(c_0_88,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_50]),c_0_67])])).

cnf(c_0_89,plain,
    ( r1_tsep_1(X1,X2)
    | ~ r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_73])).

cnf(c_0_90,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_87,c_0_88])).

cnf(c_0_91,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_92,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0)
    | ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_91]),c_0_24])])).

cnf(c_0_94,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_50]),c_0_93])])).

cnf(c_0_95,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk7_0)
    | ~ r1_tsep_1(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_96,negated_conjecture,
    ( r1_tsep_1(esk7_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_50]),c_0_67])])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_tsep_1(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_96])])).

cnf(c_0_98,negated_conjecture,
    ( ~ l1_struct_0(esk5_0)
    | ~ l1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_96]),c_0_97])).

cnf(c_0_99,negated_conjecture,
    ( ~ l1_struct_0(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_50]),c_0_93])])).

cnf(c_0_100,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_50]),c_0_67])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.53  # AutoSched0-Mode selected heuristic G_E___008_C18_F1_PI_SE_CS_SP_CO_S4S
% 0.19/0.53  # and selection function SelectNewComplexAHPNS.
% 0.19/0.53  #
% 0.19/0.53  # Preprocessing time       : 0.029 s
% 0.19/0.53  
% 0.19/0.53  # Proof found!
% 0.19/0.53  # SZS status Theorem
% 0.19/0.53  # SZS output start CNFRefutation
% 0.19/0.53  fof(t23_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_tmap_1)).
% 0.19/0.53  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.53  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.53  fof(t4_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>(r1_tarski(u1_struct_0(X2),u1_struct_0(X3))<=>m1_pre_topc(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 0.19/0.53  fof(cc1_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>v2_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 0.19/0.53  fof(dt_k1_tsep_1, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X1))&l1_pre_topc(X1))&~(v2_struct_0(X2)))&m1_pre_topc(X2,X1))&~(v2_struct_0(X3)))&m1_pre_topc(X3,X1))=>((~(v2_struct_0(k1_tsep_1(X1,X2,X3)))&v1_pre_topc(k1_tsep_1(X1,X2,X3)))&m1_pre_topc(k1_tsep_1(X1,X2,X3),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_tsep_1)).
% 0.19/0.53  fof(t22_tsep_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tsep_1)).
% 0.19/0.53  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.19/0.53  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.53  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.53  fof(symmetry_r1_tsep_1, axiom, ![X1, X2]:((l1_struct_0(X1)&l1_struct_0(X2))=>(r1_tsep_1(X1,X2)=>r1_tsep_1(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_tsep_1)).
% 0.19/0.53  fof(d2_tsep_1, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((~(v2_struct_0(X4))&v1_pre_topc(X4))&m1_pre_topc(X4,X1))=>(X4=k1_tsep_1(X1,X2,X3)<=>u1_struct_0(X4)=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tsep_1)).
% 0.19/0.53  fof(d3_tsep_1, axiom, ![X1]:(l1_struct_0(X1)=>![X2]:(l1_struct_0(X2)=>(r1_tsep_1(X1,X2)<=>r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tsep_1)).
% 0.19/0.53  fof(t70_xboole_1, axiom, ![X1, X2, X3]:(~(((~(r1_xboole_0(X1,k2_xboole_0(X2,X3)))&r1_xboole_0(X1,X2))&r1_xboole_0(X1,X3)))&~((~((r1_xboole_0(X1,X2)&r1_xboole_0(X1,X3)))&r1_xboole_0(X1,k2_xboole_0(X2,X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 0.19/0.53  fof(c_0_14, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>(m1_pre_topc(X2,X3)=>((r1_tsep_1(X2,X4)&r1_tsep_1(X4,X2))|(~(r1_tsep_1(X3,X4))&~(r1_tsep_1(X4,X3)))))))))), inference(assume_negation,[status(cth)],[t23_tmap_1])).
% 0.19/0.53  fof(c_0_15, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.53  fof(c_0_16, plain, ![X22, X23]:(~l1_pre_topc(X22)|(~m1_pre_topc(X23,X22)|l1_pre_topc(X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.53  fof(c_0_17, negated_conjecture, (((~v2_struct_0(esk4_0)&v2_pre_topc(esk4_0))&l1_pre_topc(esk4_0))&((~v2_struct_0(esk5_0)&m1_pre_topc(esk5_0,esk4_0))&((~v2_struct_0(esk6_0)&m1_pre_topc(esk6_0,esk4_0))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk4_0))&(m1_pre_topc(esk5_0,esk6_0)&((~r1_tsep_1(esk5_0,esk7_0)|~r1_tsep_1(esk7_0,esk5_0))&(r1_tsep_1(esk6_0,esk7_0)|r1_tsep_1(esk7_0,esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])).
% 0.19/0.53  fof(c_0_18, plain, ![X38, X39, X40]:((~r1_tarski(u1_struct_0(X39),u1_struct_0(X40))|m1_pre_topc(X39,X40)|~m1_pre_topc(X40,X38)|~m1_pre_topc(X39,X38)|(~v2_pre_topc(X38)|~l1_pre_topc(X38)))&(~m1_pre_topc(X39,X40)|r1_tarski(u1_struct_0(X39),u1_struct_0(X40))|~m1_pre_topc(X40,X38)|~m1_pre_topc(X39,X38)|(~v2_pre_topc(X38)|~l1_pre_topc(X38)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_tsep_1])])])])).
% 0.19/0.53  cnf(c_0_19, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.53  fof(c_0_20, plain, ![X10, X11]:(~v2_pre_topc(X10)|~l1_pre_topc(X10)|(~m1_pre_topc(X11,X10)|v2_pre_topc(X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_pre_topc])])])).
% 0.19/0.53  fof(c_0_21, plain, ![X30, X31, X32]:(((~v2_struct_0(k1_tsep_1(X30,X31,X32))|(v2_struct_0(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~m1_pre_topc(X31,X30)|v2_struct_0(X32)|~m1_pre_topc(X32,X30)))&(v1_pre_topc(k1_tsep_1(X30,X31,X32))|(v2_struct_0(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~m1_pre_topc(X31,X30)|v2_struct_0(X32)|~m1_pre_topc(X32,X30))))&(m1_pre_topc(k1_tsep_1(X30,X31,X32),X30)|(v2_struct_0(X30)|~l1_pre_topc(X30)|v2_struct_0(X31)|~m1_pre_topc(X31,X30)|v2_struct_0(X32)|~m1_pre_topc(X32,X30)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k1_tsep_1])])])])).
% 0.19/0.53  cnf(c_0_22, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.53  cnf(c_0_23, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  cnf(c_0_24, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  cnf(c_0_25, plain, (m1_pre_topc(X1,X2)|~r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.53  cnf(c_0_26, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_19])).
% 0.19/0.53  fof(c_0_27, plain, ![X35, X36, X37]:(v2_struct_0(X35)|~v2_pre_topc(X35)|~l1_pre_topc(X35)|(v2_struct_0(X36)|~m1_pre_topc(X36,X35)|(v2_struct_0(X37)|~m1_pre_topc(X37,X35)|m1_pre_topc(X36,k1_tsep_1(X35,X36,X37))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t22_tsep_1])])])])).
% 0.19/0.53  cnf(c_0_28, plain, (v2_pre_topc(X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.19/0.53  cnf(c_0_29, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  cnf(c_0_30, plain, (m1_pre_topc(k1_tsep_1(X1,X2,X3),X1)|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.53  cnf(c_0_31, negated_conjecture, (m1_pre_topc(esk5_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  cnf(c_0_32, negated_conjecture, (~v2_struct_0(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  cnf(c_0_33, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  cnf(c_0_34, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.19/0.53  cnf(c_0_35, plain, (m1_pre_topc(X1,X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~v2_pre_topc(X2)), inference(spm,[status(thm)],[c_0_25, c_0_26])).
% 0.19/0.53  fof(c_0_36, plain, ![X13, X14, X15, X17, X19]:(((r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|~m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))&((((m1_subset_1(esk1_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(X13)))|~r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))&(r2_hidden(esk1_3(X13,X14,X15),u1_pre_topc(X13))|~r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13)))&(X15=k9_subset_1(u1_struct_0(X14),esk1_3(X13,X14,X15),k2_struct_0(X14))|~r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13)))&(~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X13)))|~r2_hidden(X17,u1_pre_topc(X13))|X15!=k9_subset_1(u1_struct_0(X14),X17,k2_struct_0(X14))|r2_hidden(X15,u1_pre_topc(X14))|~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))|~m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))))&((m1_subset_1(esk2_2(X13,X14),k1_zfmisc_1(u1_struct_0(X14)))|~r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))&((~r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))|(~m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X13)))|~r2_hidden(X19,u1_pre_topc(X13))|esk2_2(X13,X14)!=k9_subset_1(u1_struct_0(X14),X19,k2_struct_0(X14)))|~r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))&(((m1_subset_1(esk3_2(X13,X14),k1_zfmisc_1(u1_struct_0(X13)))|r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))|~r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13))&(r2_hidden(esk3_2(X13,X14),u1_pre_topc(X13))|r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))|~r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13)))&(esk2_2(X13,X14)=k9_subset_1(u1_struct_0(X14),esk3_2(X13,X14),k2_struct_0(X14))|r2_hidden(esk2_2(X13,X14),u1_pre_topc(X14))|~r1_tarski(k2_struct_0(X14),k2_struct_0(X13))|m1_pre_topc(X14,X13)|~l1_pre_topc(X14)|~l1_pre_topc(X13)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.19/0.53  cnf(c_0_37, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|m1_pre_topc(X2,k1_tsep_1(X1,X2,X3))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.19/0.53  cnf(c_0_38, negated_conjecture, (v2_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_23]), c_0_24]), c_0_29])])).
% 0.19/0.53  cnf(c_0_39, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(k1_tsep_1(esk6_0,X1,esk5_0),esk6_0)|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32]), c_0_33]), c_0_34])])).
% 0.19/0.53  cnf(c_0_40, negated_conjecture, (m1_pre_topc(esk6_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_23]), c_0_24]), c_0_29])])).
% 0.19/0.53  cnf(c_0_41, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.53  cnf(c_0_42, negated_conjecture, (v2_struct_0(X1)|m1_pre_topc(X1,k1_tsep_1(esk6_0,X1,esk5_0))|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_31]), c_0_32]), c_0_33]), c_0_34]), c_0_38])])).
% 0.19/0.53  cnf(c_0_43, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0),esk6_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_32])).
% 0.19/0.53  fof(c_0_44, plain, ![X12]:(~l1_struct_0(X12)|k2_struct_0(X12)=u1_struct_0(X12)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.53  fof(c_0_45, plain, ![X21]:(~l1_pre_topc(X21)|l1_struct_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.53  cnf(c_0_46, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_41, c_0_22])).
% 0.19/0.53  cnf(c_0_47, negated_conjecture, (m1_pre_topc(esk6_0,k1_tsep_1(esk6_0,esk6_0,esk5_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_40]), c_0_32])).
% 0.19/0.53  cnf(c_0_48, negated_conjecture, (l1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_43]), c_0_34])])).
% 0.19/0.53  cnf(c_0_49, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.19/0.53  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.53  cnf(c_0_51, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.53  cnf(c_0_52, negated_conjecture, (r1_tarski(k2_struct_0(esk6_0),k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_47]), c_0_48])])).
% 0.19/0.53  cnf(c_0_53, negated_conjecture, (r1_tarski(k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0)),k2_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_43]), c_0_34])])).
% 0.19/0.53  fof(c_0_54, plain, ![X33, X34]:(~l1_struct_0(X33)|~l1_struct_0(X34)|(~r1_tsep_1(X33,X34)|r1_tsep_1(X34,X33))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[symmetry_r1_tsep_1])])).
% 0.19/0.53  cnf(c_0_55, plain, (r1_tarski(u1_struct_0(X1),u1_struct_0(X2))|~m1_pre_topc(X1,X2)|~m1_pre_topc(X2,X3)|~m1_pre_topc(X1,X3)|~v2_pre_topc(X3)|~l1_pre_topc(X3)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.53  cnf(c_0_56, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.53  cnf(c_0_57, negated_conjecture, (k2_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0))=k2_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_52]), c_0_53])])).
% 0.19/0.53  cnf(c_0_58, plain, (r1_tsep_1(X2,X1)|~l1_struct_0(X1)|~l1_struct_0(X2)|~r1_tsep_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.53  cnf(c_0_59, negated_conjecture, (r1_tsep_1(esk6_0,esk7_0)|r1_tsep_1(esk7_0,esk6_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  cnf(c_0_60, negated_conjecture, (m1_pre_topc(esk7_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  fof(c_0_61, plain, ![X24, X25, X26, X27]:((X27!=k1_tsep_1(X24,X25,X26)|u1_struct_0(X27)=k2_xboole_0(u1_struct_0(X25),u1_struct_0(X26))|(v2_struct_0(X27)|~v1_pre_topc(X27)|~m1_pre_topc(X27,X24))|(v2_struct_0(X26)|~m1_pre_topc(X26,X24))|(v2_struct_0(X25)|~m1_pre_topc(X25,X24))|(v2_struct_0(X24)|~l1_pre_topc(X24)))&(u1_struct_0(X27)!=k2_xboole_0(u1_struct_0(X25),u1_struct_0(X26))|X27=k1_tsep_1(X24,X25,X26)|(v2_struct_0(X27)|~v1_pre_topc(X27)|~m1_pre_topc(X27,X24))|(v2_struct_0(X26)|~m1_pre_topc(X26,X24))|(v2_struct_0(X25)|~m1_pre_topc(X25,X24))|(v2_struct_0(X24)|~l1_pre_topc(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d2_tsep_1])])])])])).
% 0.19/0.53  cnf(c_0_62, negated_conjecture, (r1_tarski(u1_struct_0(X1),u1_struct_0(esk6_0))|~m1_pre_topc(X1,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_40]), c_0_34]), c_0_38])])).
% 0.19/0.53  cnf(c_0_63, negated_conjecture, (u1_struct_0(k1_tsep_1(esk6_0,esk6_0,esk5_0))=k2_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_48])])).
% 0.19/0.53  cnf(c_0_64, negated_conjecture, (m1_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0),k1_tsep_1(esk6_0,esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_43]), c_0_34]), c_0_38])])).
% 0.19/0.53  cnf(c_0_65, negated_conjecture, (v2_pre_topc(k1_tsep_1(esk6_0,esk6_0,esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_43]), c_0_34]), c_0_38])])).
% 0.19/0.53  cnf(c_0_66, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)|~l1_struct_0(esk7_0)|~l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.53  cnf(c_0_67, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_60]), c_0_24])])).
% 0.19/0.53  cnf(c_0_68, plain, (u1_struct_0(X1)=k2_xboole_0(u1_struct_0(X3),u1_struct_0(X4))|v2_struct_0(X1)|v2_struct_0(X4)|v2_struct_0(X3)|v2_struct_0(X2)|X1!=k1_tsep_1(X2,X3,X4)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_pre_topc(X4,X2)|~m1_pre_topc(X3,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.19/0.53  cnf(c_0_69, plain, (v1_pre_topc(k1_tsep_1(X1,X2,X3))|v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.53  cnf(c_0_70, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|~v2_struct_0(k1_tsep_1(X1,X2,X3))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_pre_topc(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.19/0.53  cnf(c_0_71, negated_conjecture, (r1_tarski(k2_struct_0(esk6_0),u1_struct_0(esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_43]), c_0_63])).
% 0.19/0.53  cnf(c_0_72, negated_conjecture, (r1_tarski(u1_struct_0(X1),k2_struct_0(esk6_0))|~m1_pre_topc(X1,k1_tsep_1(esk6_0,esk6_0,esk5_0))), inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_55, c_0_64]), c_0_48]), c_0_65])]), c_0_63])).
% 0.19/0.53  fof(c_0_73, plain, ![X28, X29]:((~r1_tsep_1(X28,X29)|r1_xboole_0(u1_struct_0(X28),u1_struct_0(X29))|~l1_struct_0(X29)|~l1_struct_0(X28))&(~r1_xboole_0(u1_struct_0(X28),u1_struct_0(X29))|r1_tsep_1(X28,X29)|~l1_struct_0(X29)|~l1_struct_0(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tsep_1])])])])).
% 0.19/0.53  cnf(c_0_74, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)|~l1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_50]), c_0_67])])).
% 0.19/0.53  cnf(c_0_75, plain, (u1_struct_0(k1_tsep_1(X1,X2,X3))=k2_xboole_0(u1_struct_0(X2),u1_struct_0(X3))|v2_struct_0(X3)|v2_struct_0(X2)|v2_struct_0(X1)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_68]), c_0_30]), c_0_69]), c_0_70])).
% 0.19/0.53  cnf(c_0_76, negated_conjecture, (k2_struct_0(esk6_0)=u1_struct_0(esk6_0)|~r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_51, c_0_71])).
% 0.19/0.53  cnf(c_0_77, negated_conjecture, (r1_tarski(u1_struct_0(esk6_0),k2_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_72, c_0_47])).
% 0.19/0.53  cnf(c_0_78, plain, (r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~r1_tsep_1(X1,X2)|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.53  cnf(c_0_79, negated_conjecture, (r1_tsep_1(esk7_0,esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_50]), c_0_34])])).
% 0.19/0.53  fof(c_0_80, plain, ![X7, X8, X9]:((r1_xboole_0(X7,k2_xboole_0(X8,X9))|~r1_xboole_0(X7,X8)|~r1_xboole_0(X7,X9))&((r1_xboole_0(X7,X8)|~r1_xboole_0(X7,k2_xboole_0(X8,X9)))&(r1_xboole_0(X7,X9)|~r1_xboole_0(X7,k2_xboole_0(X8,X9))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t70_xboole_1])])])])).
% 0.19/0.53  cnf(c_0_81, negated_conjecture, (k2_xboole_0(u1_struct_0(X1),u1_struct_0(esk5_0))=u1_struct_0(k1_tsep_1(esk6_0,X1,esk5_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk6_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_31]), c_0_34])]), c_0_33]), c_0_32])).
% 0.19/0.53  cnf(c_0_82, negated_conjecture, (k2_struct_0(esk6_0)=u1_struct_0(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_76, c_0_77])])).
% 0.19/0.53  cnf(c_0_83, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))|~l1_struct_0(esk6_0)|~l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.19/0.53  cnf(c_0_84, plain, (r1_xboole_0(X1,X2)|~r1_xboole_0(X1,k2_xboole_0(X3,X2))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.19/0.53  cnf(c_0_85, negated_conjecture, (k2_xboole_0(u1_struct_0(esk6_0),u1_struct_0(esk5_0))=u1_struct_0(esk6_0)), inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_40]), c_0_63]), c_0_82]), c_0_32])).
% 0.19/0.53  cnf(c_0_86, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))|~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_50]), c_0_34])])).
% 0.19/0.53  cnf(c_0_87, negated_conjecture, (r1_xboole_0(X1,u1_struct_0(esk5_0))|~r1_xboole_0(X1,u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_84, c_0_85])).
% 0.19/0.53  cnf(c_0_88, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86, c_0_50]), c_0_67])])).
% 0.19/0.53  cnf(c_0_89, plain, (r1_tsep_1(X1,X2)|~r1_xboole_0(u1_struct_0(X1),u1_struct_0(X2))|~l1_struct_0(X2)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_73])).
% 0.19/0.53  cnf(c_0_90, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_87, c_0_88])).
% 0.19/0.53  cnf(c_0_91, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  cnf(c_0_92, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)|~l1_struct_0(esk5_0)|~l1_struct_0(esk7_0)), inference(spm,[status(thm)],[c_0_89, c_0_90])).
% 0.19/0.53  cnf(c_0_93, negated_conjecture, (l1_pre_topc(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_91]), c_0_24])])).
% 0.19/0.53  cnf(c_0_94, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)|~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92, c_0_50]), c_0_93])])).
% 0.19/0.53  cnf(c_0_95, negated_conjecture, (~r1_tsep_1(esk5_0,esk7_0)|~r1_tsep_1(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.53  cnf(c_0_96, negated_conjecture, (r1_tsep_1(esk7_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94, c_0_50]), c_0_67])])).
% 0.19/0.53  cnf(c_0_97, negated_conjecture, (~r1_tsep_1(esk5_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95, c_0_96])])).
% 0.19/0.53  cnf(c_0_98, negated_conjecture, (~l1_struct_0(esk5_0)|~l1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_96]), c_0_97])).
% 0.19/0.53  cnf(c_0_99, negated_conjecture, (~l1_struct_0(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98, c_0_50]), c_0_93])])).
% 0.19/0.53  cnf(c_0_100, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99, c_0_50]), c_0_67])]), ['proof']).
% 0.19/0.53  # SZS output end CNFRefutation
% 0.19/0.53  # Proof object total steps             : 101
% 0.19/0.53  # Proof object clause steps            : 72
% 0.19/0.53  # Proof object formula steps           : 29
% 0.19/0.53  # Proof object conjectures             : 52
% 0.19/0.53  # Proof object clause conjectures      : 49
% 0.19/0.53  # Proof object formula conjectures     : 3
% 0.19/0.53  # Proof object initial clauses used    : 28
% 0.19/0.53  # Proof object initial formulas used   : 14
% 0.19/0.53  # Proof object generating inferences   : 39
% 0.19/0.53  # Proof object simplifying inferences  : 81
% 0.19/0.53  # Training examples: 0 positive, 0 negative
% 0.19/0.53  # Parsed axioms                        : 14
% 0.19/0.53  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.53  # Initial clauses                      : 43
% 0.19/0.53  # Removed in clause preprocessing      : 0
% 0.19/0.53  # Initial clauses in saturation        : 43
% 0.19/0.53  # Processed clauses                    : 1311
% 0.19/0.53  # ...of these trivial                  : 40
% 0.19/0.53  # ...subsumed                          : 162
% 0.19/0.53  # ...remaining for further processing  : 1109
% 0.19/0.53  # Other redundant clauses eliminated   : 4
% 0.19/0.53  # Clauses deleted for lack of memory   : 0
% 0.19/0.53  # Backward-subsumed                    : 49
% 0.19/0.53  # Backward-rewritten                   : 117
% 0.19/0.53  # Generated clauses                    : 8266
% 0.19/0.53  # ...of the previous two non-trivial   : 7445
% 0.19/0.53  # Contextual simplify-reflections      : 8
% 0.19/0.53  # Paramodulations                      : 8262
% 0.19/0.53  # Factorizations                       : 0
% 0.19/0.53  # Equation resolutions                 : 4
% 0.19/0.53  # Propositional unsat checks           : 0
% 0.19/0.53  #    Propositional check models        : 0
% 0.19/0.53  #    Propositional check unsatisfiable : 0
% 0.19/0.53  #    Propositional clauses             : 0
% 0.19/0.53  #    Propositional clauses after purity: 0
% 0.19/0.53  #    Propositional unsat core size     : 0
% 0.19/0.53  #    Propositional preprocessing time  : 0.000
% 0.19/0.53  #    Propositional encoding time       : 0.000
% 0.19/0.53  #    Propositional solver time         : 0.000
% 0.19/0.53  #    Success case prop preproc time    : 0.000
% 0.19/0.53  #    Success case prop encoding time   : 0.000
% 0.19/0.53  #    Success case prop solver time     : 0.000
% 0.19/0.53  # Current number of processed clauses  : 939
% 0.19/0.53  #    Positive orientable unit clauses  : 207
% 0.19/0.53  #    Positive unorientable unit clauses: 0
% 0.19/0.53  #    Negative unit clauses             : 6
% 0.19/0.53  #    Non-unit-clauses                  : 726
% 0.19/0.53  # Current number of unprocessed clauses: 6040
% 0.19/0.53  # ...number of literals in the above   : 23412
% 0.19/0.53  # Current number of archived formulas  : 0
% 0.19/0.53  # Current number of archived clauses   : 166
% 0.19/0.53  # Clause-clause subsumption calls (NU) : 74734
% 0.19/0.53  # Rec. Clause-clause subsumption calls : 49098
% 0.19/0.53  # Non-unit clause-clause subsumptions  : 219
% 0.19/0.53  # Unit Clause-clause subsumption calls : 2988
% 0.19/0.53  # Rewrite failures with RHS unbound    : 0
% 0.19/0.53  # BW rewrite match attempts            : 359
% 0.19/0.53  # BW rewrite match successes           : 26
% 0.19/0.53  # Condensation attempts                : 1311
% 0.19/0.53  # Condensation successes               : 0
% 0.19/0.53  # Termbank termtop insertions          : 269595
% 0.36/0.53  
% 0.36/0.53  # -------------------------------------------------
% 0.36/0.53  # User time                : 0.178 s
% 0.36/0.53  # System time              : 0.011 s
% 0.36/0.53  # Total time               : 0.189 s
% 0.36/0.53  # Maximum resident set size: 1596 pages
%------------------------------------------------------------------------------
