%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:16:47 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 495 expanded)
%              Number of clauses        :   55 ( 191 expanded)
%              Number of leaves         :   11 ( 121 expanded)
%              Depth                    :   15
%              Number of atoms          :  442 (3979 expanded)
%              Number of equality atoms :   30 ( 286 expanded)
%              Maximal formula depth    :   27 (   5 average)
%              Maximal clause size      :   90 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t13_tmap_1,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X3 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
               => ( ( v1_borsuk_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> ( v1_borsuk_1(X3,X1)
                    & m1_pre_topc(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_tmap_1)).

fof(t60_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v3_pre_topc(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
        <=> ( v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(t11_tsep_1,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = u1_struct_0(X2)
               => ( ( v1_borsuk_1(X2,X1)
                    & m1_pre_topc(X2,X1) )
                <=> v4_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).

fof(t12_tmap_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( X2 = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
               => ( m1_pre_topc(X2,X1)
                <=> m1_pre_topc(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_tmap_1)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v2_pre_topc(X3)
                  & l1_pre_topc(X3) )
               => ( X3 = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                 => ( ( v1_borsuk_1(X2,X1)
                      & m1_pre_topc(X2,X1) )
                  <=> ( v1_borsuk_1(X3,X1)
                      & m1_pre_topc(X3,X1) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t13_tmap_1])).

fof(c_0_12,plain,(
    ! [X21,X22] :
      ( ( v3_pre_topc(X22,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | ~ v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))))
        | ~ v3_pre_topc(X22,X21)
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( v3_pre_topc(X22,X21)
        | ~ v3_pre_topc(X22,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))
        | ~ v3_pre_topc(X22,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | ~ m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).

fof(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v2_pre_topc(esk6_0)
    & l1_pre_topc(esk6_0)
    & esk6_0 = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))
    & ( ~ v1_borsuk_1(esk5_0,esk4_0)
      | ~ m1_pre_topc(esk5_0,esk4_0)
      | ~ v1_borsuk_1(esk6_0,esk4_0)
      | ~ m1_pre_topc(esk6_0,esk4_0) )
    & ( v1_borsuk_1(esk6_0,esk4_0)
      | v1_borsuk_1(esk5_0,esk4_0) )
    & ( m1_pre_topc(esk6_0,esk4_0)
      | v1_borsuk_1(esk5_0,esk4_0) )
    & ( v1_borsuk_1(esk6_0,esk4_0)
      | m1_pre_topc(esk5_0,esk4_0) )
    & ( m1_pre_topc(esk6_0,esk4_0)
      | m1_pre_topc(esk5_0,esk4_0) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X7] : m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_15,plain,(
    ! [X6] : k2_subset_1(X6) = X6 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_16,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( esk6_0 = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X8,X9] :
      ( ( ~ m1_subset_1(X8,k1_zfmisc_1(X9))
        | r1_tarski(X8,X9) )
      & ( ~ r1_tarski(X8,X9)
        | m1_subset_1(X8,k1_zfmisc_1(X9)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v3_pre_topc(X1,esk6_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_16,c_0_17]),c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_21])).

cnf(c_0_25,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_26,plain,(
    ! [X4,X5] :
      ( ( r1_tarski(X4,X5)
        | X4 != X5 )
      & ( r1_tarski(X5,X4)
        | X4 != X5 )
      & ( ~ r1_tarski(X4,X5)
        | ~ r1_tarski(X5,X4)
        | X4 = X5 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_27,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk6_0) ),
    inference(pm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_25,c_0_17]),c_0_18]),c_0_19])])).

fof(c_0_30,plain,(
    ! [X17,X18] :
      ( ( ~ v3_pre_topc(X18,X17)
        | r2_hidden(X18,u1_pre_topc(X17))
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) )
      & ( ~ r2_hidden(X18,u1_pre_topc(X17))
        | v3_pre_topc(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_pre_topc(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk6_0),u1_struct_0(esk5_0))
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk6_0) ),
    inference(pm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk6_0))
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(pm,[status(thm)],[c_0_27,c_0_29])).

cnf(c_0_34,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_35,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

fof(c_0_36,plain,(
    ! [X10,X11,X12,X13] :
      ( ( r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ r1_tarski(X11,u1_pre_topc(X10))
        | r2_hidden(k5_setfam_1(u1_struct_0(X10),X11),u1_pre_topc(X10))
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ r2_hidden(X12,u1_pre_topc(X10))
        | ~ r2_hidden(X13,u1_pre_topc(X10))
        | r2_hidden(k9_subset_1(u1_struct_0(X10),X12,X13),u1_pre_topc(X10))
        | ~ v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk2_1(X10),k1_zfmisc_1(u1_struct_0(X10)))
        | m1_subset_1(esk1_1(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk3_1(X10),k1_zfmisc_1(u1_struct_0(X10)))
        | m1_subset_1(esk1_1(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(esk2_1(X10),u1_pre_topc(X10))
        | m1_subset_1(esk1_1(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(esk3_1(X10),u1_pre_topc(X10))
        | m1_subset_1(esk1_1(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X10),esk2_1(X10),esk3_1(X10)),u1_pre_topc(X10))
        | m1_subset_1(esk1_1(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk2_1(X10),k1_zfmisc_1(u1_struct_0(X10)))
        | r1_tarski(esk1_1(X10),u1_pre_topc(X10))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk3_1(X10),k1_zfmisc_1(u1_struct_0(X10)))
        | r1_tarski(esk1_1(X10),u1_pre_topc(X10))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(esk2_1(X10),u1_pre_topc(X10))
        | r1_tarski(esk1_1(X10),u1_pre_topc(X10))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(esk3_1(X10),u1_pre_topc(X10))
        | r1_tarski(esk1_1(X10),u1_pre_topc(X10))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X10),esk2_1(X10),esk3_1(X10)),u1_pre_topc(X10))
        | r1_tarski(esk1_1(X10),u1_pre_topc(X10))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk2_1(X10),k1_zfmisc_1(u1_struct_0(X10)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( m1_subset_1(esk3_1(X10),k1_zfmisc_1(u1_struct_0(X10)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(esk2_1(X10),u1_pre_topc(X10))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( r2_hidden(esk3_1(X10),u1_pre_topc(X10))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X10),esk2_1(X10),esk3_1(X10)),u1_pre_topc(X10))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))
        | ~ r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))
        | v2_pre_topc(X10)
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_37,plain,(
    ! [X25,X26,X27] :
      ( ( ~ v1_borsuk_1(X26,X25)
        | ~ m1_pre_topc(X26,X25)
        | v4_pre_topc(X27,X25)
        | X27 != u1_struct_0(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_pre_topc(X26,X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( v1_borsuk_1(X26,X25)
        | ~ v4_pre_topc(X27,X25)
        | X27 != u1_struct_0(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_pre_topc(X26,X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) )
      & ( m1_pre_topc(X26,X25)
        | ~ v4_pre_topc(X27,X25)
        | X27 != u1_struct_0(X26)
        | ~ m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ m1_pre_topc(X26,X25)
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tsep_1])])])])).

cnf(c_0_38,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk5_0)
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk6_0)
    | ~ r1_tarski(u1_struct_0(esk5_0),u1_struct_0(esk6_0)) ),
    inference(pm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk6_0))
    | ~ v3_pre_topc(X1,esk5_0)
    | ~ r1_tarski(X1,u1_struct_0(esk5_0)) ),
    inference(pm,[status(thm)],[c_0_33,c_0_34])).

cnf(c_0_40,plain,
    ( r1_tarski(X1,X1) ),
    inference(pm,[status(thm)],[c_0_27,c_0_24])).

cnf(c_0_41,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ l1_pre_topc(X2)
    | ~ r1_tarski(X1,u1_struct_0(X2)) ),
    inference(pm,[status(thm)],[c_0_35,c_0_34])).

cnf(c_0_42,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_43,plain,
    ( v4_pre_topc(X3,X2)
    | ~ v1_borsuk_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_44,plain,(
    ! [X28,X29,X30] :
      ( ( ~ m1_pre_topc(X29,X28)
        | m1_pre_topc(X30,X28)
        | X29 != g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30))
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) )
      & ( ~ m1_pre_topc(X30,X28)
        | m1_pre_topc(X29,X28)
        | X29 != g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30))
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30)
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).

cnf(c_0_45,plain,
    ( v1_borsuk_1(X1,X2)
    | ~ v4_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

fof(c_0_46,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X31)
      | m1_subset_1(u1_struct_0(X32),k1_zfmisc_1(u1_struct_0(X31))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_47,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk5_0)
    | ~ v3_pre_topc(u1_struct_0(esk6_0),esk6_0)
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_38,c_0_39]),c_0_40])])).

cnf(c_0_48,plain,
    ( v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41,c_0_42]),c_0_40])])).

cnf(c_0_49,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_50,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_51,plain,
    ( v4_pre_topc(X3,X2)
    | X3 != u1_struct_0(X1)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_borsuk_1(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(cn,[status(thm)],[c_0_43])).

cnf(c_0_52,plain,
    ( m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | X1 != g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_53,plain,
    ( v1_borsuk_1(X1,X2)
    | ~ v4_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_54,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk5_0)
    | ~ v3_pre_topc(u1_struct_0(esk5_0),esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50])])).

cnf(c_0_56,plain,
    ( v4_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_borsuk_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(er,[status(thm)],[c_0_51])).

cnf(c_0_57,negated_conjecture,
    ( m1_pre_topc(esk5_0,X1)
    | esk6_0 != X2
    | ~ m1_pre_topc(X2,X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_58,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk4_0)
    | m1_pre_topc(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_59,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_60,plain,
    ( v1_borsuk_1(X1,X2)
    | ~ v4_pre_topc(u1_struct_0(X1),X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(pm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_61,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55,c_0_48]),c_0_18]),c_0_19])])).

cnf(c_0_62,plain,
    ( v4_pre_topc(u1_struct_0(X1),X2)
    | ~ v1_borsuk_1(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(pm,[status(thm)],[c_0_56,c_0_54])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_borsuk_1(esk5_0,esk4_0)
    | ~ m1_pre_topc(esk5_0,esk4_0)
    | ~ v1_borsuk_1(esk6_0,esk4_0)
    | ~ m1_pre_topc(esk6_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(esk5_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_57,c_0_58]),c_0_49]),c_0_59]),c_0_50])])).

cnf(c_0_65,negated_conjecture,
    ( v1_borsuk_1(esk6_0,X1)
    | ~ v4_pre_topc(u1_struct_0(esk5_0),X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( v4_pre_topc(u1_struct_0(esk5_0),X1)
    | ~ v1_borsuk_1(esk6_0,X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_borsuk_1(esk5_0,esk4_0)
    | ~ v1_borsuk_1(esk6_0,esk4_0)
    | ~ m1_pre_topc(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63,c_0_64])])).

cnf(c_0_68,negated_conjecture,
    ( v1_borsuk_1(esk6_0,X1)
    | ~ v1_borsuk_1(esk5_0,X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_65,c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_70,negated_conjecture,
    ( v1_borsuk_1(esk5_0,X1)
    | ~ v1_borsuk_1(esk6_0,X1)
    | ~ m1_pre_topc(esk5_0,X1)
    | ~ m1_pre_topc(esk6_0,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(pm,[status(thm)],[c_0_60,c_0_66])).

cnf(c_0_71,negated_conjecture,
    ( v1_borsuk_1(esk6_0,esk4_0)
    | v1_borsuk_1(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_72,negated_conjecture,
    ( ~ v1_borsuk_1(esk5_0,esk4_0)
    | ~ m1_pre_topc(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_67,c_0_68]),c_0_64]),c_0_69]),c_0_59])])).

cnf(c_0_73,negated_conjecture,
    ( v1_borsuk_1(esk5_0,esk4_0)
    | ~ m1_pre_topc(esk6_0,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70,c_0_71]),c_0_64]),c_0_69]),c_0_59])])).

cnf(c_0_74,plain,
    ( m1_pre_topc(X3,X2)
    | ~ m1_pre_topc(X1,X2)
    | X3 != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_75,negated_conjecture,
    ( ~ m1_pre_topc(esk6_0,esk4_0) ),
    inference(pm,[status(thm)],[c_0_72,c_0_73])).

cnf(c_0_76,negated_conjecture,
    ( m1_pre_topc(X1,X2)
    | esk6_0 != X1
    | ~ m1_pre_topc(esk5_0,X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74,c_0_17]),c_0_18]),c_0_19])])).

cnf(c_0_77,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75,c_0_76]),c_0_64]),c_0_49]),c_0_50]),c_0_59])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  # Version: 2.5pre002
% 0.14/0.34  # No SInE strategy applied
% 0.14/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.47  # AutoSched0-Mode selected heuristic G_E___300_C01_S00
% 0.20/0.47  # and selection function NoSelection.
% 0.20/0.47  #
% 0.20/0.47  # Preprocessing time       : 0.029 s
% 0.20/0.47  
% 0.20/0.47  # Proof found!
% 0.20/0.47  # SZS status Theorem
% 0.20/0.47  # SZS output start CNFRefutation
% 0.20/0.47  fof(t13_tmap_1, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X3=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>((v1_borsuk_1(X2,X1)&m1_pre_topc(X2,X1))<=>(v1_borsuk_1(X3,X1)&m1_pre_topc(X3,X1))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_tmap_1)).
% 0.20/0.47  fof(t60_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v3_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 0.20/0.47  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.20/0.47  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 0.20/0.47  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.47  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.47  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.20/0.47  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.20/0.47  fof(t11_tsep_1, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>((v1_borsuk_1(X2,X1)&m1_pre_topc(X2,X1))<=>v4_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tsep_1)).
% 0.20/0.47  fof(t12_tmap_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X2=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))=>(m1_pre_topc(X2,X1)<=>m1_pre_topc(X3,X1)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_tmap_1)).
% 0.20/0.47  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.20/0.47  fof(c_0_11, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:((v2_pre_topc(X3)&l1_pre_topc(X3))=>(X3=g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=>((v1_borsuk_1(X2,X1)&m1_pre_topc(X2,X1))<=>(v1_borsuk_1(X3,X1)&m1_pre_topc(X3,X1)))))))), inference(assume_negation,[status(cth)],[t13_tmap_1])).
% 0.20/0.47  fof(c_0_12, plain, ![X21, X22]:(((v3_pre_topc(X22,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|(~v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21))))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))))|(~v3_pre_topc(X22,X21)|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21))))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))&((v3_pre_topc(X22,X21)|(~v3_pre_topc(X22,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21))))))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(X21)))|(~v3_pre_topc(X22,g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|~m1_subset_1(X22,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21))))))|(~v2_pre_topc(X21)|~l1_pre_topc(X21))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).
% 0.20/0.47  fof(c_0_13, negated_conjecture, ((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&((v2_pre_topc(esk5_0)&l1_pre_topc(esk5_0))&((v2_pre_topc(esk6_0)&l1_pre_topc(esk6_0))&(esk6_0=g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))&((~v1_borsuk_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|(~v1_borsuk_1(esk6_0,esk4_0)|~m1_pre_topc(esk6_0,esk4_0)))&(((v1_borsuk_1(esk6_0,esk4_0)|v1_borsuk_1(esk5_0,esk4_0))&(m1_pre_topc(esk6_0,esk4_0)|v1_borsuk_1(esk5_0,esk4_0)))&((v1_borsuk_1(esk6_0,esk4_0)|m1_pre_topc(esk5_0,esk4_0))&(m1_pre_topc(esk6_0,esk4_0)|m1_pre_topc(esk5_0,esk4_0))))))))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_11])])])])).
% 0.20/0.47  fof(c_0_14, plain, ![X7]:m1_subset_1(k2_subset_1(X7),k1_zfmisc_1(X7)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.20/0.47  fof(c_0_15, plain, ![X6]:k2_subset_1(X6)=X6, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.20/0.47  cnf(c_0_16, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.47  cnf(c_0_17, negated_conjecture, (esk6_0=g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_20, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.47  cnf(c_0_21, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.20/0.47  fof(c_0_22, plain, ![X8, X9]:((~m1_subset_1(X8,k1_zfmisc_1(X9))|r1_tarski(X8,X9))&(~r1_tarski(X8,X9)|m1_subset_1(X8,k1_zfmisc_1(X9)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.47  cnf(c_0_23, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))|~v3_pre_topc(X1,esk6_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_16, c_0_17]), c_0_17]), c_0_18]), c_0_19])])).
% 0.20/0.47  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.47  cnf(c_0_25, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.47  fof(c_0_26, plain, ![X4, X5]:(((r1_tarski(X4,X5)|X4!=X5)&(r1_tarski(X5,X4)|X4!=X5))&(~r1_tarski(X4,X5)|~r1_tarski(X5,X4)|X4=X5)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.47  cnf(c_0_27, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_28, negated_conjecture, (m1_subset_1(u1_struct_0(esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))|~v3_pre_topc(u1_struct_0(esk6_0),esk6_0)), inference(pm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.47  cnf(c_0_29, negated_conjecture, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk6_0)))|~v3_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_25, c_0_17]), c_0_18]), c_0_19])])).
% 0.20/0.47  fof(c_0_30, plain, ![X17, X18]:((~v3_pre_topc(X18,X17)|r2_hidden(X18,u1_pre_topc(X17))|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))&(~r2_hidden(X18,u1_pre_topc(X17))|v3_pre_topc(X18,X17)|~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))|~l1_pre_topc(X17))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.20/0.47  cnf(c_0_31, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.47  cnf(c_0_32, negated_conjecture, (r1_tarski(u1_struct_0(esk6_0),u1_struct_0(esk5_0))|~v3_pre_topc(u1_struct_0(esk6_0),esk6_0)), inference(pm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.47  cnf(c_0_33, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk6_0))|~v3_pre_topc(X1,esk5_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(pm,[status(thm)],[c_0_27, c_0_29])).
% 0.20/0.47  cnf(c_0_34, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.20/0.47  cnf(c_0_35, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.47  fof(c_0_36, plain, ![X10, X11, X12, X13]:((((r2_hidden(u1_struct_0(X10),u1_pre_topc(X10))|~v2_pre_topc(X10)|~l1_pre_topc(X10))&(~m1_subset_1(X11,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|(~r1_tarski(X11,u1_pre_topc(X10))|r2_hidden(k5_setfam_1(u1_struct_0(X10),X11),u1_pre_topc(X10)))|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X10)))|(~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X10)))|(~r2_hidden(X12,u1_pre_topc(X10))|~r2_hidden(X13,u1_pre_topc(X10))|r2_hidden(k9_subset_1(u1_struct_0(X10),X12,X13),u1_pre_topc(X10))))|~v2_pre_topc(X10)|~l1_pre_topc(X10)))&(((m1_subset_1(esk2_1(X10),k1_zfmisc_1(u1_struct_0(X10)))|(m1_subset_1(esk1_1(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10))&((m1_subset_1(esk3_1(X10),k1_zfmisc_1(u1_struct_0(X10)))|(m1_subset_1(esk1_1(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10))&(((r2_hidden(esk2_1(X10),u1_pre_topc(X10))|(m1_subset_1(esk1_1(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10))&(r2_hidden(esk3_1(X10),u1_pre_topc(X10))|(m1_subset_1(esk1_1(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10)))&(~r2_hidden(k9_subset_1(u1_struct_0(X10),esk2_1(X10),esk3_1(X10)),u1_pre_topc(X10))|(m1_subset_1(esk1_1(X10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X10))))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10)))))&(((m1_subset_1(esk2_1(X10),k1_zfmisc_1(u1_struct_0(X10)))|(r1_tarski(esk1_1(X10),u1_pre_topc(X10))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10))&((m1_subset_1(esk3_1(X10),k1_zfmisc_1(u1_struct_0(X10)))|(r1_tarski(esk1_1(X10),u1_pre_topc(X10))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10))&(((r2_hidden(esk2_1(X10),u1_pre_topc(X10))|(r1_tarski(esk1_1(X10),u1_pre_topc(X10))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10))&(r2_hidden(esk3_1(X10),u1_pre_topc(X10))|(r1_tarski(esk1_1(X10),u1_pre_topc(X10))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10)))&(~r2_hidden(k9_subset_1(u1_struct_0(X10),esk2_1(X10),esk3_1(X10)),u1_pre_topc(X10))|(r1_tarski(esk1_1(X10),u1_pre_topc(X10))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10)))))&((m1_subset_1(esk2_1(X10),k1_zfmisc_1(u1_struct_0(X10)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10))&((m1_subset_1(esk3_1(X10),k1_zfmisc_1(u1_struct_0(X10)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10))&(((r2_hidden(esk2_1(X10),u1_pre_topc(X10))|(~r2_hidden(k5_setfam_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10))&(r2_hidden(esk3_1(X10),u1_pre_topc(X10))|(~r2_hidden(k5_setfam_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10)))&(~r2_hidden(k9_subset_1(u1_struct_0(X10),esk2_1(X10),esk3_1(X10)),u1_pre_topc(X10))|(~r2_hidden(k5_setfam_1(u1_struct_0(X10),esk1_1(X10)),u1_pre_topc(X10))|~r2_hidden(u1_struct_0(X10),u1_pre_topc(X10)))|v2_pre_topc(X10)|~l1_pre_topc(X10)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.20/0.47  fof(c_0_37, plain, ![X25, X26, X27]:((~v1_borsuk_1(X26,X25)|~m1_pre_topc(X26,X25)|v4_pre_topc(X27,X25)|X27!=u1_struct_0(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|~m1_pre_topc(X26,X25)|(~v2_pre_topc(X25)|~l1_pre_topc(X25)))&((v1_borsuk_1(X26,X25)|~v4_pre_topc(X27,X25)|X27!=u1_struct_0(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|~m1_pre_topc(X26,X25)|(~v2_pre_topc(X25)|~l1_pre_topc(X25)))&(m1_pre_topc(X26,X25)|~v4_pre_topc(X27,X25)|X27!=u1_struct_0(X26)|~m1_subset_1(X27,k1_zfmisc_1(u1_struct_0(X25)))|~m1_pre_topc(X26,X25)|(~v2_pre_topc(X25)|~l1_pre_topc(X25))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t11_tsep_1])])])])).
% 0.20/0.47  cnf(c_0_38, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk5_0)|~v3_pre_topc(u1_struct_0(esk6_0),esk6_0)|~r1_tarski(u1_struct_0(esk5_0),u1_struct_0(esk6_0))), inference(pm,[status(thm)],[c_0_31, c_0_32])).
% 0.20/0.47  cnf(c_0_39, negated_conjecture, (r1_tarski(X1,u1_struct_0(esk6_0))|~v3_pre_topc(X1,esk5_0)|~r1_tarski(X1,u1_struct_0(esk5_0))), inference(pm,[status(thm)],[c_0_33, c_0_34])).
% 0.20/0.47  cnf(c_0_40, plain, (r1_tarski(X1,X1)), inference(pm,[status(thm)],[c_0_27, c_0_24])).
% 0.20/0.47  cnf(c_0_41, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~l1_pre_topc(X2)|~r1_tarski(X1,u1_struct_0(X2))), inference(pm,[status(thm)],[c_0_35, c_0_34])).
% 0.20/0.47  cnf(c_0_42, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.20/0.47  cnf(c_0_43, plain, (v4_pre_topc(X3,X2)|~v1_borsuk_1(X1,X2)|~m1_pre_topc(X1,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.47  fof(c_0_44, plain, ![X28, X29, X30]:((~m1_pre_topc(X29,X28)|m1_pre_topc(X30,X28)|X29!=g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30))|(~v2_pre_topc(X30)|~l1_pre_topc(X30))|(~v2_pre_topc(X29)|~l1_pre_topc(X29))|~l1_pre_topc(X28))&(~m1_pre_topc(X30,X28)|m1_pre_topc(X29,X28)|X29!=g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30))|(~v2_pre_topc(X30)|~l1_pre_topc(X30))|(~v2_pre_topc(X29)|~l1_pre_topc(X29))|~l1_pre_topc(X28))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t12_tmap_1])])])])).
% 0.20/0.47  cnf(c_0_45, plain, (v1_borsuk_1(X1,X2)|~v4_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.47  fof(c_0_46, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_pre_topc(X32,X31)|m1_subset_1(u1_struct_0(X32),k1_zfmisc_1(u1_struct_0(X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.20/0.47  cnf(c_0_47, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk5_0)|~v3_pre_topc(u1_struct_0(esk6_0),esk6_0)|~v3_pre_topc(u1_struct_0(esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_38, c_0_39]), c_0_40])])).
% 0.20/0.47  cnf(c_0_48, plain, (v3_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_41, c_0_42]), c_0_40])])).
% 0.20/0.47  cnf(c_0_49, negated_conjecture, (v2_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_50, negated_conjecture, (l1_pre_topc(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_51, plain, (v4_pre_topc(X3,X2)|X3!=u1_struct_0(X1)|~l1_pre_topc(X2)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X2)|~v1_borsuk_1(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(cn,[status(thm)],[c_0_43])).
% 0.20/0.47  cnf(c_0_52, plain, (m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|X1!=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.47  cnf(c_0_53, plain, (v1_borsuk_1(X1,X2)|~v4_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_45])).
% 0.20/0.47  cnf(c_0_54, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.20/0.47  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk5_0)|~v3_pre_topc(u1_struct_0(esk5_0),esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50])])).
% 0.20/0.47  cnf(c_0_56, plain, (v4_pre_topc(u1_struct_0(X1),X2)|~v1_borsuk_1(X1,X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X2)))), inference(er,[status(thm)],[c_0_51])).
% 0.20/0.47  cnf(c_0_57, negated_conjecture, (m1_pre_topc(esk5_0,X1)|esk6_0!=X2|~m1_pre_topc(X2,X1)|~v2_pre_topc(X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_52, c_0_17]), c_0_18]), c_0_19])])).
% 0.20/0.47  cnf(c_0_58, negated_conjecture, (m1_pre_topc(esk6_0,esk4_0)|m1_pre_topc(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_59, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_60, plain, (v1_borsuk_1(X1,X2)|~v4_pre_topc(u1_struct_0(X1),X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(pm,[status(thm)],[c_0_53, c_0_54])).
% 0.20/0.47  cnf(c_0_61, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_55, c_0_48]), c_0_18]), c_0_19])])).
% 0.20/0.47  cnf(c_0_62, plain, (v4_pre_topc(u1_struct_0(X1),X2)|~v1_borsuk_1(X1,X2)|~m1_pre_topc(X1,X2)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(pm,[status(thm)],[c_0_56, c_0_54])).
% 0.20/0.47  cnf(c_0_63, negated_conjecture, (~v1_borsuk_1(esk5_0,esk4_0)|~m1_pre_topc(esk5_0,esk4_0)|~v1_borsuk_1(esk6_0,esk4_0)|~m1_pre_topc(esk6_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_64, negated_conjecture, (m1_pre_topc(esk5_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_57, c_0_58]), c_0_49]), c_0_59]), c_0_50])])).
% 0.20/0.47  cnf(c_0_65, negated_conjecture, (v1_borsuk_1(esk6_0,X1)|~v4_pre_topc(u1_struct_0(esk5_0),X1)|~m1_pre_topc(esk6_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.47  cnf(c_0_66, negated_conjecture, (v4_pre_topc(u1_struct_0(esk5_0),X1)|~v1_borsuk_1(esk6_0,X1)|~m1_pre_topc(esk6_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_62, c_0_61])).
% 0.20/0.47  cnf(c_0_67, negated_conjecture, (~v1_borsuk_1(esk5_0,esk4_0)|~v1_borsuk_1(esk6_0,esk4_0)|~m1_pre_topc(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_63, c_0_64])])).
% 0.20/0.47  cnf(c_0_68, negated_conjecture, (v1_borsuk_1(esk6_0,X1)|~v1_borsuk_1(esk5_0,X1)|~m1_pre_topc(esk6_0,X1)|~m1_pre_topc(esk5_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_65, c_0_62])).
% 0.20/0.47  cnf(c_0_69, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_70, negated_conjecture, (v1_borsuk_1(esk5_0,X1)|~v1_borsuk_1(esk6_0,X1)|~m1_pre_topc(esk5_0,X1)|~m1_pre_topc(esk6_0,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(pm,[status(thm)],[c_0_60, c_0_66])).
% 0.20/0.47  cnf(c_0_71, negated_conjecture, (v1_borsuk_1(esk6_0,esk4_0)|v1_borsuk_1(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.47  cnf(c_0_72, negated_conjecture, (~v1_borsuk_1(esk5_0,esk4_0)|~m1_pre_topc(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_67, c_0_68]), c_0_64]), c_0_69]), c_0_59])])).
% 0.20/0.47  cnf(c_0_73, negated_conjecture, (v1_borsuk_1(esk5_0,esk4_0)|~m1_pre_topc(esk6_0,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_70, c_0_71]), c_0_64]), c_0_69]), c_0_59])])).
% 0.20/0.47  cnf(c_0_74, plain, (m1_pre_topc(X3,X2)|~m1_pre_topc(X1,X2)|X3!=g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.47  cnf(c_0_75, negated_conjecture, (~m1_pre_topc(esk6_0,esk4_0)), inference(pm,[status(thm)],[c_0_72, c_0_73])).
% 0.20/0.47  cnf(c_0_76, negated_conjecture, (m1_pre_topc(X1,X2)|esk6_0!=X1|~m1_pre_topc(esk5_0,X2)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_74, c_0_17]), c_0_18]), c_0_19])])).
% 0.20/0.47  cnf(c_0_77, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(pm,[status(thm)],[c_0_75, c_0_76]), c_0_64]), c_0_49]), c_0_50]), c_0_59])]), ['proof']).
% 0.20/0.47  # SZS output end CNFRefutation
% 0.20/0.47  # Proof object total steps             : 78
% 0.20/0.47  # Proof object clause steps            : 55
% 0.20/0.47  # Proof object formula steps           : 23
% 0.20/0.47  # Proof object conjectures             : 35
% 0.20/0.47  # Proof object clause conjectures      : 32
% 0.20/0.47  # Proof object formula conjectures     : 3
% 0.20/0.47  # Proof object initial clauses used    : 24
% 0.20/0.47  # Proof object initial formulas used   : 11
% 0.20/0.47  # Proof object generating inferences   : 28
% 0.20/0.47  # Proof object simplifying inferences  : 44
% 0.20/0.47  # Training examples: 0 positive, 0 negative
% 0.20/0.47  # Parsed axioms                        : 13
% 0.20/0.47  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.47  # Initial clauses                      : 52
% 0.20/0.47  # Removed in clause preprocessing      : 2
% 0.20/0.47  # Initial clauses in saturation        : 50
% 0.20/0.47  # Processed clauses                    : 720
% 0.20/0.47  # ...of these trivial                  : 14
% 0.20/0.47  # ...subsumed                          : 337
% 0.20/0.47  # ...remaining for further processing  : 369
% 0.20/0.47  # Other redundant clauses eliminated   : 0
% 0.20/0.47  # Clauses deleted for lack of memory   : 0
% 0.20/0.47  # Backward-subsumed                    : 34
% 0.20/0.47  # Backward-rewritten                   : 40
% 0.20/0.47  # Generated clauses                    : 3354
% 0.20/0.47  # ...of the previous two non-trivial   : 2750
% 0.20/0.47  # Contextual simplify-reflections      : 0
% 0.20/0.47  # Paramodulations                      : 3315
% 0.20/0.47  # Factorizations                       : 0
% 0.20/0.47  # Equation resolutions                 : 38
% 0.20/0.47  # Propositional unsat checks           : 0
% 0.20/0.47  #    Propositional check models        : 0
% 0.20/0.47  #    Propositional check unsatisfiable : 0
% 0.20/0.47  #    Propositional clauses             : 0
% 0.20/0.47  #    Propositional clauses after purity: 0
% 0.20/0.47  #    Propositional unsat core size     : 0
% 0.20/0.47  #    Propositional preprocessing time  : 0.000
% 0.20/0.47  #    Propositional encoding time       : 0.000
% 0.20/0.47  #    Propositional solver time         : 0.000
% 0.20/0.47  #    Success case prop preproc time    : 0.000
% 0.20/0.47  #    Success case prop encoding time   : 0.000
% 0.20/0.47  #    Success case prop solver time     : 0.000
% 0.20/0.47  # Current number of processed clauses  : 294
% 0.20/0.47  #    Positive orientable unit clauses  : 16
% 0.20/0.47  #    Positive unorientable unit clauses: 0
% 0.20/0.47  #    Negative unit clauses             : 1
% 0.20/0.47  #    Non-unit-clauses                  : 277
% 0.20/0.47  # Current number of unprocessed clauses: 1998
% 0.20/0.47  # ...number of literals in the above   : 15825
% 0.20/0.47  # Current number of archived formulas  : 0
% 0.20/0.47  # Current number of archived clauses   : 76
% 0.20/0.47  # Clause-clause subsumption calls (NU) : 7501
% 0.20/0.47  # Rec. Clause-clause subsumption calls : 2080
% 0.20/0.47  # Non-unit clause-clause subsumptions  : 371
% 0.20/0.47  # Unit Clause-clause subsumption calls : 127
% 0.20/0.47  # Rewrite failures with RHS unbound    : 0
% 0.20/0.47  # BW rewrite match attempts            : 6
% 0.20/0.47  # BW rewrite match successes           : 5
% 0.20/0.47  # Condensation attempts                : 0
% 0.20/0.47  # Condensation successes               : 0
% 0.20/0.47  # Termbank termtop insertions          : 54874
% 0.20/0.47  
% 0.20/0.47  # -------------------------------------------------
% 0.20/0.47  # User time                : 0.117 s
% 0.20/0.47  # System time              : 0.013 s
% 0.20/0.47  # Total time               : 0.130 s
% 0.20/0.47  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
