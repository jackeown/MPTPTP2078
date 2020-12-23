%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1388+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:13 EST 2020

% Result     : Theorem 0.21s
% Output     : CNFRefutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 (1630 expanded)
%              Number of clauses        :   65 ( 656 expanded)
%              Number of leaves         :   11 ( 415 expanded)
%              Depth                    :   19
%              Number of atoms          :  413 (8566 expanded)
%              Number of equality atoms :   32 ( 476 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   31 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(t24_connsp_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ! [X4] :
                  ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( X3 = X4
                   => ( v2_connsp_1(X3,X1)
                    <=> v2_connsp_1(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_connsp_1)).

fof(t39_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(t13_connsp_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( ( v3_connsp_1(X2,X1)
                  & r1_tarski(X2,X3) )
               => r3_connsp_1(X1,X3,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_connsp_2)).

fof(d5_connsp_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_connsp_1(X2,X1)
          <=> ( v2_connsp_1(X2,X1)
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( v2_connsp_1(X3,X1)
                      & r1_tarski(X2,X3) )
                   => X2 = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_connsp_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d6_connsp_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( r3_connsp_1(X1,X2,X3)
              <=> ? [X4] :
                    ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
                    & X4 = X3
                    & v3_connsp_1(X4,k1_pre_topc(X1,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_connsp_1)).

fof(c_0_11,plain,(
    ! [X8] :
      ( ~ l1_struct_0(X8)
      | k2_struct_0(X8) = u1_struct_0(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_12,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | l1_struct_0(X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_13,plain,(
    ! [X5,X6,X7] :
      ( ( X7 != k1_pre_topc(X5,X6)
        | k2_struct_0(X7) = X6
        | ~ v1_pre_topc(X7)
        | ~ m1_pre_topc(X7,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) )
      & ( k2_struct_0(X7) != X6
        | X7 = k1_pre_topc(X5,X6)
        | ~ v1_pre_topc(X7)
        | ~ m1_pre_topc(X7,X5)
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X5) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_14,plain,(
    ! [X18,X19] :
      ( ( v1_pre_topc(k1_pre_topc(X18,X19))
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))) )
      & ( m1_pre_topc(k1_pre_topc(X18,X19),X18)
        | ~ l1_pre_topc(X18)
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

fof(c_0_15,plain,(
    ! [X21,X22] :
      ( ~ l1_pre_topc(X21)
      | ~ m1_pre_topc(X22,X21)
      | l1_pre_topc(X22) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_16,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ v2_connsp_1(X25,X23)
        | v2_connsp_1(X26,X24)
        | X25 != X26
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X24,X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) )
      & ( ~ v2_connsp_1(X26,X24)
        | v2_connsp_1(X25,X23)
        | X25 != X26
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X24)))
        | ~ m1_subset_1(X25,k1_zfmisc_1(u1_struct_0(X23)))
        | ~ m1_pre_topc(X24,X23)
        | ~ v2_pre_topc(X23)
        | ~ l1_pre_topc(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t24_connsp_1])])])])).

fof(c_0_17,plain,(
    ! [X27,X28,X29] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,X27)
      | ~ m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X28)))
      | m1_subset_1(X29,k1_zfmisc_1(u1_struct_0(X27))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t39_pre_topc])])])).

cnf(c_0_18,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_19,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_24,plain,
    ( v2_connsp_1(X3,X4)
    | ~ v2_connsp_1(X1,X2)
    | X1 != X3
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X4,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_26,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_27,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_20]),c_0_21]),c_0_22])).

cnf(c_0_28,plain,
    ( l1_pre_topc(k1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_22])).

fof(c_0_29,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( ( v3_connsp_1(X2,X1)
                    & r1_tarski(X2,X3) )
                 => r3_connsp_1(X1,X3,X2) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_connsp_2])).

fof(c_0_30,plain,(
    ! [X9,X10,X11] :
      ( ( v2_connsp_1(X10,X9)
        | ~ v3_connsp_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ v2_connsp_1(X11,X9)
        | ~ r1_tarski(X10,X11)
        | X10 = X11
        | ~ v3_connsp_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk1_2(X9,X10),k1_zfmisc_1(u1_struct_0(X9)))
        | ~ v2_connsp_1(X10,X9)
        | v3_connsp_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( v2_connsp_1(esk1_2(X9,X10),X9)
        | ~ v2_connsp_1(X10,X9)
        | v3_connsp_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( r1_tarski(X10,esk1_2(X9,X10))
        | ~ v2_connsp_1(X10,X9)
        | v3_connsp_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) )
      & ( X10 != esk1_2(X9,X10)
        | ~ v2_connsp_1(X10,X9)
        | v3_connsp_1(X10,X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_connsp_1])])])])])).

cnf(c_0_31,plain,
    ( v2_connsp_1(X1,X2)
    | ~ v2_pre_topc(X3)
    | ~ v2_connsp_1(X1,X3)
    | ~ m1_pre_topc(X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X3) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_24]),c_0_25])).

cnf(c_0_32,plain,
    ( u1_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_28])).

fof(c_0_33,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0)))
    & v3_connsp_1(esk4_0,esk3_0)
    & r1_tarski(esk4_0,esk5_0)
    & ~ r3_connsp_1(esk3_0,esk5_0,esk4_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_29])])])])).

cnf(c_0_34,plain,
    ( v2_connsp_1(esk1_2(X1,X2),X1)
    | v3_connsp_1(X2,X1)
    | ~ v2_connsp_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,plain,
    ( v2_connsp_1(X1,k1_pre_topc(X2,X3))
    | ~ v2_pre_topc(X4)
    | ~ v2_connsp_1(X1,X4)
    | ~ m1_pre_topc(k1_pre_topc(X2,X3),X4)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_37,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,plain,
    ( m1_subset_1(esk1_2(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | v3_connsp_1(X2,X1)
    | ~ v2_connsp_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,esk1_2(X2,X1))
    | v3_connsp_1(X1,X2)
    | ~ v2_connsp_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_40,plain,
    ( v2_connsp_1(X3,X4)
    | ~ v2_connsp_1(X1,X2)
    | X3 != X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
    | ~ m1_pre_topc(X2,X4)
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,plain,
    ( v2_connsp_1(esk1_2(k1_pre_topc(X1,X2),X3),k1_pre_topc(X1,X2))
    | v3_connsp_1(X3,k1_pre_topc(X1,X2))
    | ~ v2_connsp_1(X3,k1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_32]),c_0_28])).

cnf(c_0_42,negated_conjecture,
    ( v2_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | ~ v2_pre_topc(X2)
    | ~ v2_connsp_1(X1,X2)
    | ~ m1_pre_topc(k1_pre_topc(esk3_0,esk5_0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0))
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])])).

cnf(c_0_43,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_44,plain,(
    ! [X30,X31] :
      ( ( ~ m1_subset_1(X30,k1_zfmisc_1(X31))
        | r1_tarski(X30,X31) )
      & ( ~ r1_tarski(X30,X31)
        | m1_subset_1(X30,k1_zfmisc_1(X31)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_45,plain,
    ( v3_connsp_1(X1,k1_pre_topc(X2,X3))
    | m1_subset_1(esk1_2(k1_pre_topc(X2,X3),X1),k1_zfmisc_1(X3))
    | ~ v2_connsp_1(X1,k1_pre_topc(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_32]),c_0_28])).

cnf(c_0_46,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(k1_pre_topc(X3,X4),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_25,c_0_32])).

cnf(c_0_47,plain,
    ( r1_tarski(X1,esk1_2(k1_pre_topc(X2,X3),X1))
    | v3_connsp_1(X1,k1_pre_topc(X2,X3))
    | ~ v2_connsp_1(X1,k1_pre_topc(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X3))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_32]),c_0_28])).

cnf(c_0_48,plain,
    ( v2_connsp_1(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_connsp_1(X1,X3)
    | ~ m1_pre_topc(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_40]),c_0_25])).

cnf(c_0_49,negated_conjecture,
    ( v2_connsp_1(esk1_2(k1_pre_topc(esk3_0,esk5_0),X1),k1_pre_topc(esk3_0,esk5_0))
    | v3_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | ~ v2_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_36]),c_0_37])])).

cnf(c_0_50,negated_conjecture,
    ( v2_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | ~ v2_connsp_1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_22]),c_0_43]),c_0_37]),c_0_36])])).

cnf(c_0_51,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( r1_tarski(esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_53,plain,
    ( v2_connsp_1(X1,X2)
    | ~ v3_connsp_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_54,negated_conjecture,
    ( v3_connsp_1(esk4_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_55,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_56,negated_conjecture,
    ( v3_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | m1_subset_1(esk1_2(k1_pre_topc(esk3_0,esk5_0),X1),k1_zfmisc_1(esk5_0))
    | ~ v2_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_36]),c_0_37])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(k1_pre_topc(esk3_0,esk5_0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0))
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_36]),c_0_37])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(X1,esk1_2(k1_pre_topc(esk3_0,esk5_0),X1))
    | v3_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | ~ v2_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_36]),c_0_37])])).

cnf(c_0_59,plain,
    ( v2_connsp_1(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_connsp_1(X1,k1_pre_topc(X3,X4))
    | ~ m1_pre_topc(k1_pre_topc(X3,X4),X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X4))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X3) ),
    inference(spm,[status(thm)],[c_0_48,c_0_32])).

cnf(c_0_60,negated_conjecture,
    ( v2_connsp_1(esk1_2(k1_pre_topc(esk3_0,esk5_0),X1),k1_pre_topc(esk3_0,esk5_0))
    | v3_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | ~ v2_connsp_1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_61,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,negated_conjecture,
    ( v2_connsp_1(esk4_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55]),c_0_37])])).

cnf(c_0_63,negated_conjecture,
    ( v3_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | m1_subset_1(esk1_2(k1_pre_topc(esk3_0,esk5_0),X1),k1_zfmisc_1(esk5_0))
    | ~ v2_connsp_1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_56,c_0_50])).

cnf(c_0_64,plain,
    ( X3 = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_connsp_1(X1,X2)
    | ~ r1_tarski(X3,X1)
    | ~ v3_connsp_1(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_65,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_22]),c_0_37]),c_0_36])])).

cnf(c_0_66,negated_conjecture,
    ( r1_tarski(X1,esk1_2(k1_pre_topc(esk3_0,esk5_0),X1))
    | v3_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | ~ v2_connsp_1(X1,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_58,c_0_50])).

cnf(c_0_67,negated_conjecture,
    ( v2_connsp_1(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_connsp_1(X1,k1_pre_topc(esk3_0,esk5_0))
    | ~ m1_pre_topc(k1_pre_topc(esk3_0,esk5_0),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk5_0))
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_36]),c_0_37])])).

cnf(c_0_68,negated_conjecture,
    ( v2_connsp_1(esk1_2(k1_pre_topc(esk3_0,esk5_0),esk4_0),k1_pre_topc(esk3_0,esk5_0))
    | v3_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62])])).

cnf(c_0_69,negated_conjecture,
    ( v3_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0))
    | m1_subset_1(esk1_2(k1_pre_topc(esk3_0,esk5_0),esk4_0),k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_61]),c_0_62])])).

cnf(c_0_70,negated_conjecture,
    ( X1 = X2
    | ~ r1_tarski(X2,X1)
    | ~ v2_connsp_1(X1,esk3_0)
    | ~ v3_connsp_1(X2,esk3_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_37])])).

cnf(c_0_71,negated_conjecture,
    ( r1_tarski(esk4_0,esk1_2(k1_pre_topc(esk3_0,esk5_0),esk4_0))
    | v3_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_61]),c_0_62])])).

cnf(c_0_72,negated_conjecture,
    ( v2_connsp_1(esk1_2(k1_pre_topc(esk3_0,esk5_0),esk4_0),X1)
    | v3_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0))
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(k1_pre_topc(esk3_0,esk5_0),X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_73,negated_conjecture,
    ( esk1_2(k1_pre_topc(esk3_0,esk5_0),esk4_0) = esk4_0
    | v3_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0))
    | ~ v2_connsp_1(esk1_2(k1_pre_topc(esk3_0,esk5_0),esk4_0),esk3_0)
    | ~ m1_subset_1(esk1_2(k1_pre_topc(esk3_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_54]),c_0_61])])).

cnf(c_0_74,negated_conjecture,
    ( v2_connsp_1(esk1_2(k1_pre_topc(esk3_0,esk5_0),esk4_0),esk3_0)
    | v3_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_22]),c_0_43]),c_0_37]),c_0_36])])).

fof(c_0_75,plain,(
    ! [X13,X14,X15,X17] :
      ( ( m1_subset_1(esk2_3(X13,X14,X15),k1_zfmisc_1(u1_struct_0(k1_pre_topc(X13,X14))))
        | ~ r3_connsp_1(X13,X14,X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( esk2_3(X13,X14,X15) = X15
        | ~ r3_connsp_1(X13,X14,X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( v3_connsp_1(esk2_3(X13,X14,X15),k1_pre_topc(X13,X14))
        | ~ r3_connsp_1(X13,X14,X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) )
      & ( ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X13,X14))))
        | X17 != X15
        | ~ v3_connsp_1(X17,k1_pre_topc(X13,X14))
        | r3_connsp_1(X13,X14,X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_pre_topc(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d6_connsp_1])])])])])).

cnf(c_0_76,negated_conjecture,
    ( esk1_2(k1_pre_topc(esk3_0,esk5_0),esk4_0) = esk4_0
    | v3_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0))
    | ~ m1_subset_1(esk1_2(k1_pre_topc(esk3_0,esk5_0),esk4_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,plain,
    ( r3_connsp_1(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X2,X3))))
    | X1 != X4
    | ~ v3_connsp_1(X1,k1_pre_topc(X2,X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_78,negated_conjecture,
    ( esk1_2(k1_pre_topc(esk3_0,esk5_0),esk4_0) = esk4_0
    | v3_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_65]),c_0_69])).

cnf(c_0_79,plain,
    ( r3_connsp_1(X1,X2,X3)
    | ~ v3_connsp_1(X3,k1_pre_topc(X1,X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k1_pre_topc(X1,X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(er,[status(thm)],[c_0_77])).

cnf(c_0_80,negated_conjecture,
    ( v2_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0))
    | v3_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( ~ r3_connsp_1(esk3_0,esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_82,plain,
    ( v3_connsp_1(X1,X2)
    | X1 != esk1_2(X2,X1)
    | ~ v2_connsp_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_83,negated_conjecture,
    ( v2_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk3_0,esk5_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_55]),c_0_36]),c_0_37])]),c_0_81])).

cnf(c_0_84,negated_conjecture,
    ( v3_connsp_1(esk4_0,k1_pre_topc(esk3_0,esk5_0))
    | ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk3_0,esk5_0))))
    | ~ l1_pre_topc(k1_pre_topc(esk3_0,esk5_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_78]),c_0_83])).

cnf(c_0_85,negated_conjecture,
    ( ~ m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(k1_pre_topc(esk3_0,esk5_0))))
    | ~ l1_pre_topc(k1_pre_topc(esk3_0,esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_84]),c_0_55]),c_0_36]),c_0_37])]),c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( ~ l1_pre_topc(k1_pre_topc(esk3_0,esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_32]),c_0_61]),c_0_36]),c_0_37])])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_28]),c_0_36]),c_0_37])]),
    [proof]).

%------------------------------------------------------------------------------
