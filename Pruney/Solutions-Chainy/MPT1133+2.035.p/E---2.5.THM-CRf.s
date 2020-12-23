%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:26 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 (1089 expanded)
%              Number of clauses        :   66 ( 456 expanded)
%              Number of leaves         :   11 ( 270 expanded)
%              Depth                    :   17
%              Number of atoms          :  545 (8653 expanded)
%              Number of equality atoms :   26 ( 552 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :   90 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

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

fof(fc6_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(t64_pre_topc,conjecture,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(t62_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(t63_pre_topc,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                 => ( X3 = X4
                   => ( v5_pre_topc(X3,X1,X2)
                    <=> v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(dt_g1_pre_topc,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))
     => ( v1_pre_topc(g1_pre_topc(X1,X2))
        & l1_pre_topc(g1_pre_topc(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(dt_u1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(c_0_11,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

fof(c_0_12,plain,(
    ! [X7,X8] :
      ( ( ~ m1_subset_1(X7,k1_zfmisc_1(X8))
        | r1_tarski(X7,X8) )
      & ( ~ r1_tarski(X7,X8)
        | m1_subset_1(X7,k1_zfmisc_1(X8)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_13,plain,(
    ! [X22,X23] :
      ( ( v3_pre_topc(X23,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ v3_pre_topc(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))))
        | ~ v3_pre_topc(X23,X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( v3_pre_topc(X23,X22)
        | ~ v3_pre_topc(X23,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))))
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) )
      & ( m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ v3_pre_topc(X23,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))))
        | ~ v2_pre_topc(X22)
        | ~ l1_pre_topc(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).

fof(c_0_14,plain,(
    ! [X16,X17] :
      ( ( ~ v3_pre_topc(X17,X16)
        | r2_hidden(X17,u1_pre_topc(X16))
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) )
      & ( ~ r2_hidden(X17,u1_pre_topc(X16))
        | v3_pre_topc(X17,X16)
        | ~ m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))
        | ~ l1_pre_topc(X16) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_15,plain,
    ( r1_tarski(X1,X2)
    | X2 != X1 ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,plain,
    ( r1_tarski(X1,X1) ),
    inference(er,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r1_tarski(X1,X2) ),
    inference(spm,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

cnf(c_0_24,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_20,c_0_21])).

fof(c_0_25,plain,(
    ! [X9,X10,X11,X12] :
      ( ( r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r1_tarski(X10,u1_pre_topc(X9))
        | r2_hidden(k5_setfam_1(u1_struct_0(X9),X10),u1_pre_topc(X9))
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ r2_hidden(X11,u1_pre_topc(X9))
        | ~ r2_hidden(X12,u1_pre_topc(X9))
        | r2_hidden(k9_subset_1(u1_struct_0(X9),X11,X12),u1_pre_topc(X9))
        | ~ v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk2_1(X9),u1_pre_topc(X9))
        | m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk3_1(X9),u1_pre_topc(X9))
        | m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))
        | m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | r1_tarski(esk1_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | r1_tarski(esk1_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk2_1(X9),u1_pre_topc(X9))
        | r1_tarski(esk1_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk3_1(X9),u1_pre_topc(X9))
        | r1_tarski(esk1_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))
        | r1_tarski(esk1_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk2_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( r2_hidden(esk3_1(X9),u1_pre_topc(X9))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) )
      & ( ~ r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))
        | ~ r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))
        | v2_pre_topc(X9)
        | ~ l1_pre_topc(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).

fof(c_0_26,plain,(
    ! [X21] :
      ( ( v1_pre_topc(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) )
      & ( v2_pre_topc(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))
        | ~ v2_pre_topc(X21)
        | ~ l1_pre_topc(X21) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).

fof(c_0_27,negated_conjecture,(
    ~ ! [X1] :
        ( ( v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))) )
                   => ( X3 = X4
                     => ( v5_pre_topc(X3,X1,X2)
                      <=> v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t64_pre_topc])).

cnf(c_0_28,plain,
    ( X1 = X2
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_17])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_30,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_31,plain,
    ( r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_33,plain,(
    ! [X24,X25,X26,X27] :
      ( ( ~ v5_pre_topc(X26,X24,X25)
        | v5_pre_topc(X27,g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24)),X25)
        | X26 != X27
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))),u1_struct_0(X25))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))),u1_struct_0(X25))))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25))))
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) )
      & ( ~ v5_pre_topc(X27,g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24)),X25)
        | v5_pre_topc(X26,X24,X25)
        | X26 != X27
        | ~ v1_funct_1(X27)
        | ~ v1_funct_2(X27,u1_struct_0(g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))),u1_struct_0(X25))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))),u1_struct_0(X25))))
        | ~ v1_funct_1(X26)
        | ~ v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))
        | ~ m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25))))
        | ~ v2_pre_topc(X25)
        | ~ l1_pre_topc(X25)
        | ~ v2_pre_topc(X24)
        | ~ l1_pre_topc(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).

fof(c_0_34,negated_conjecture,
    ( v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))
    & esk6_0 = esk7_0
    & ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
      | ~ v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) )
    & ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
      | v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).

cnf(c_0_35,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = X2
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_36,plain,
    ( m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32])).

fof(c_0_37,plain,(
    ! [X28,X29,X30,X31] :
      ( ( ~ v5_pre_topc(X30,X28,X29)
        | v5_pre_topc(X31,X28,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))
        | X30 != X31
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X28),u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29))))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29))))))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) )
      & ( ~ v5_pre_topc(X31,X28,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))
        | v5_pre_topc(X30,X28,X29)
        | X30 != X31
        | ~ v1_funct_1(X31)
        | ~ v1_funct_2(X31,u1_struct_0(X28),u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29))))
        | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29))))))
        | ~ v1_funct_1(X30)
        | ~ v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))
        | ~ m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
        | ~ v2_pre_topc(X29)
        | ~ l1_pre_topc(X29)
        | ~ v2_pre_topc(X28)
        | ~ l1_pre_topc(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).

cnf(c_0_38,plain,
    ( v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | X1 != X4
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ v3_pre_topc(u1_struct_0(X1),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_24])])).

fof(c_0_43,plain,(
    ! [X18,X19] :
      ( ( v1_pre_topc(g1_pre_topc(X18,X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18))) )
      & ( l1_pre_topc(g1_pre_topc(X18,X19))
        | ~ m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).

fof(c_0_44,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(X20)
      | m1_subset_1(u1_pre_topc(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).

cnf(c_0_45,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_47,plain,
    ( v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_38])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(rw,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(rw,[status(thm)],[c_0_41,c_0_40])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_51,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_52,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_53,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_19]),c_0_24])]),c_0_31])).

cnf(c_0_54,plain,
    ( l1_pre_topc(g1_pre_topc(X1,X2))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_45])).

cnf(c_0_57,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_58,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_59,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_60,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_46,c_0_40])).

cnf(c_0_61,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49]),c_0_50]),c_0_51]),c_0_52])])).

cnf(c_0_62,plain,
    ( v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | X1 != X4
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_63,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) = u1_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | ~ v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_48]),c_0_49]),c_0_50]),c_0_57]),c_0_58])])).

cnf(c_0_65,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_59,c_0_40])).

cnf(c_0_66,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_67,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_68,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_69,plain,
    ( v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))
    | ~ v5_pre_topc(X1,X2,X3)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_62])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_63]),c_0_51]),c_0_52])])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_63]),c_0_51]),c_0_52])])).

cnf(c_0_72,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_65])).

cnf(c_0_73,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_63]),c_0_67]),c_0_68]),c_0_57]),c_0_58])])).

cnf(c_0_74,negated_conjecture,
    ( v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_67]),c_0_50]),c_0_57]),c_0_51]),c_0_58]),c_0_52]),c_0_68])])).

cnf(c_0_75,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_32]),c_0_51]),c_0_52])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_77,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))
    | ~ m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0)))) ),
    inference(spm,[status(thm)],[c_0_75,c_0_54])).

cnf(c_0_78,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_32]),c_0_57]),c_0_58])])).

cnf(c_0_79,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))
    | ~ m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_55]),c_0_52])])).

cnf(c_0_80,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0)
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0)))) ),
    inference(spm,[status(thm)],[c_0_78,c_0_54])).

cnf(c_0_81,plain,
    ( v5_pre_topc(X4,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | X4 != X1
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_82,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)
    | v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_63]),c_0_67]),c_0_68]),c_0_51]),c_0_52])])).

cnf(c_0_83,negated_conjecture,
    ( ~ v5_pre_topc(esk6_0,esk4_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_55]),c_0_58])])).

cnf(c_0_84,plain,
    ( v5_pre_topc(X1,X2,X3)
    | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)
    | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) ),
    inference(er,[status(thm)],[c_0_81])).

cnf(c_0_85,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_63]),c_0_57]),c_0_58])])).

cnf(c_0_86,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_63]),c_0_57]),c_0_58])])).

cnf(c_0_87,negated_conjecture,
    ( v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0) ),
    inference(sr,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_67]),c_0_50]),c_0_57]),c_0_51]),c_0_58]),c_0_52]),c_0_68])]),c_0_87])]),c_0_83]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:16:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  # Version: 2.5pre002
% 0.14/0.35  # No SInE strategy applied
% 0.14/0.35  # Trying AutoSched0 for 299 seconds
% 0.20/0.41  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.41  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.41  #
% 0.20/0.41  # Preprocessing time       : 0.044 s
% 0.20/0.41  
% 0.20/0.41  # Proof found!
% 0.20/0.41  # SZS status Theorem
% 0.20/0.41  # SZS output start CNFRefutation
% 0.20/0.41  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.20/0.41  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.41  fof(t60_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v3_pre_topc(X2,X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))<=>(v3_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_pre_topc)).
% 0.20/0.41  fof(d5_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v3_pre_topc(X2,X1)<=>r2_hidden(X2,u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_pre_topc)).
% 0.20/0.41  fof(d1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>(v2_pre_topc(X1)<=>((r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))=>(r1_tarski(X2,u1_pre_topc(X1))=>r2_hidden(k5_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)))))&![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>((r2_hidden(X2,u1_pre_topc(X1))&r2_hidden(X3,u1_pre_topc(X1)))=>r2_hidden(k9_subset_1(u1_struct_0(X1),X2,X3),u1_pre_topc(X1)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_pre_topc)).
% 0.20/0.41  fof(fc6_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>(v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))&v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 0.20/0.41  fof(t64_pre_topc, conjecture, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_pre_topc)).
% 0.20/0.41  fof(t62_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_pre_topc)).
% 0.20/0.41  fof(t63_pre_topc, axiom, ![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_pre_topc)).
% 0.20/0.41  fof(dt_g1_pre_topc, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))=>(v1_pre_topc(g1_pre_topc(X1,X2))&l1_pre_topc(g1_pre_topc(X1,X2)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 0.20/0.41  fof(dt_u1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 0.20/0.41  fof(c_0_11, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.20/0.41  fof(c_0_12, plain, ![X7, X8]:((~m1_subset_1(X7,k1_zfmisc_1(X8))|r1_tarski(X7,X8))&(~r1_tarski(X7,X8)|m1_subset_1(X7,k1_zfmisc_1(X8)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.41  fof(c_0_13, plain, ![X22, X23]:(((v3_pre_topc(X23,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))|(~v3_pre_topc(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))))|(~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))))|(~v3_pre_topc(X23,X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))))|(~v2_pre_topc(X22)|~l1_pre_topc(X22))))&((v3_pre_topc(X23,X22)|(~v3_pre_topc(X23,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22))))))|(~v2_pre_topc(X22)|~l1_pre_topc(X22)))&(m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|(~v3_pre_topc(X23,g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22)))|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X22),u1_pre_topc(X22))))))|(~v2_pre_topc(X22)|~l1_pre_topc(X22))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t60_pre_topc])])])])).
% 0.20/0.41  fof(c_0_14, plain, ![X16, X17]:((~v3_pre_topc(X17,X16)|r2_hidden(X17,u1_pre_topc(X16))|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))&(~r2_hidden(X17,u1_pre_topc(X16))|v3_pre_topc(X17,X16)|~m1_subset_1(X17,k1_zfmisc_1(u1_struct_0(X16)))|~l1_pre_topc(X16))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).
% 0.20/0.41  cnf(c_0_15, plain, (r1_tarski(X1,X2)|X2!=X1), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_16, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.41  cnf(c_0_17, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_18, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v3_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_19, plain, (v3_pre_topc(X1,X2)|~r2_hidden(X1,u1_pre_topc(X2))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.20/0.41  cnf(c_0_20, plain, (m1_subset_1(X1,k1_zfmisc_1(X2))|~r1_tarski(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.20/0.41  cnf(c_0_21, plain, (r1_tarski(X1,X1)), inference(er,[status(thm)],[c_0_15])).
% 0.20/0.41  cnf(c_0_22, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~r1_tarski(X1,X2)), inference(spm,[status(thm)],[c_0_16, c_0_17])).
% 0.20/0.41  cnf(c_0_23, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~r2_hidden(X1,u1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))|~v2_pre_topc(X2)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), inference(spm,[status(thm)],[c_0_18, c_0_19])).
% 0.20/0.41  cnf(c_0_24, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_20, c_0_21])).
% 0.20/0.41  fof(c_0_25, plain, ![X9, X10, X11, X12]:((((r2_hidden(u1_struct_0(X9),u1_pre_topc(X9))|~v2_pre_topc(X9)|~l1_pre_topc(X9))&(~m1_subset_1(X10,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|(~r1_tarski(X10,u1_pre_topc(X9))|r2_hidden(k5_setfam_1(u1_struct_0(X9),X10),u1_pre_topc(X9)))|~v2_pre_topc(X9)|~l1_pre_topc(X9)))&(~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))|(~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X9)))|(~r2_hidden(X11,u1_pre_topc(X9))|~r2_hidden(X12,u1_pre_topc(X9))|r2_hidden(k9_subset_1(u1_struct_0(X9),X11,X12),u1_pre_topc(X9))))|~v2_pre_topc(X9)|~l1_pre_topc(X9)))&(((m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&((m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(((r2_hidden(esk2_1(X9),u1_pre_topc(X9))|(m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(r2_hidden(esk3_1(X9),u1_pre_topc(X9))|(m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))&(~r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))|(m1_subset_1(esk1_1(X9),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X9))))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))))&(((m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(r1_tarski(esk1_1(X9),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&((m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(r1_tarski(esk1_1(X9),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(((r2_hidden(esk2_1(X9),u1_pre_topc(X9))|(r1_tarski(esk1_1(X9),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(r2_hidden(esk3_1(X9),u1_pre_topc(X9))|(r1_tarski(esk1_1(X9),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))&(~r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))|(r1_tarski(esk1_1(X9),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))))&((m1_subset_1(esk2_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&((m1_subset_1(esk3_1(X9),k1_zfmisc_1(u1_struct_0(X9)))|(~r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(((r2_hidden(esk2_1(X9),u1_pre_topc(X9))|(~r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9))&(r2_hidden(esk3_1(X9),u1_pre_topc(X9))|(~r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))&(~r2_hidden(k9_subset_1(u1_struct_0(X9),esk2_1(X9),esk3_1(X9)),u1_pre_topc(X9))|(~r2_hidden(k5_setfam_1(u1_struct_0(X9),esk1_1(X9)),u1_pre_topc(X9))|~r2_hidden(u1_struct_0(X9),u1_pre_topc(X9)))|v2_pre_topc(X9)|~l1_pre_topc(X9)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_pre_topc])])])])])).
% 0.20/0.41  fof(c_0_26, plain, ![X21]:((v1_pre_topc(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))&(v2_pre_topc(g1_pre_topc(u1_struct_0(X21),u1_pre_topc(X21)))|(~v2_pre_topc(X21)|~l1_pre_topc(X21)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_pre_topc])])])).
% 0.20/0.41  fof(c_0_27, negated_conjecture, ~(![X1]:((v2_pre_topc(X1)&l1_pre_topc(X1))=>![X2]:((v2_pre_topc(X2)&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))=>(X3=X4=>(v5_pre_topc(X3,X1,X2)<=>v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))))))), inference(assume_negation,[status(cth)],[t64_pre_topc])).
% 0.20/0.41  cnf(c_0_28, plain, (X1=X2|~m1_subset_1(X2,k1_zfmisc_1(X1))|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(spm,[status(thm)],[c_0_22, c_0_17])).
% 0.20/0.41  cnf(c_0_29, plain, (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))|~v3_pre_topc(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.20/0.41  cnf(c_0_30, plain, (m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))|~v2_pre_topc(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_23, c_0_24])).
% 0.20/0.41  cnf(c_0_31, plain, (r2_hidden(u1_struct_0(X1),u1_pre_topc(X1))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.20/0.41  cnf(c_0_32, plain, (v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.20/0.41  fof(c_0_33, plain, ![X24, X25, X26, X27]:((~v5_pre_topc(X26,X24,X25)|v5_pre_topc(X27,g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24)),X25)|X26!=X27|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))),u1_struct_0(X25))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))),u1_struct_0(X25)))))|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25)))))|(~v2_pre_topc(X25)|~l1_pre_topc(X25))|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))&(~v5_pre_topc(X27,g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24)),X25)|v5_pre_topc(X26,X24,X25)|X26!=X27|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))),u1_struct_0(X25))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X24),u1_pre_topc(X24))),u1_struct_0(X25)))))|(~v1_funct_1(X26)|~v1_funct_2(X26,u1_struct_0(X24),u1_struct_0(X25))|~m1_subset_1(X26,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X24),u1_struct_0(X25)))))|(~v2_pre_topc(X25)|~l1_pre_topc(X25))|(~v2_pre_topc(X24)|~l1_pre_topc(X24)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t62_pre_topc])])])])).
% 0.20/0.41  fof(c_0_34, negated_conjecture, ((v2_pre_topc(esk4_0)&l1_pre_topc(esk4_0))&((v2_pre_topc(esk5_0)&l1_pre_topc(esk5_0))&(((v1_funct_1(esk6_0)&v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0)))&m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0)))))&(((v1_funct_1(esk7_0)&v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))&m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))))&(esk6_0=esk7_0&((~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))&(v5_pre_topc(esk6_0,esk4_0,esk5_0)|v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_27])])])).
% 0.20/0.41  cnf(c_0_35, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=X2|~v3_pre_topc(X2,X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(X2))|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(spm,[status(thm)],[c_0_28, c_0_29])).
% 0.20/0.41  cnf(c_0_36, plain, (m1_subset_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),k1_zfmisc_1(u1_struct_0(X1)))|~v2_pre_topc(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_30, c_0_31]), c_0_32])).
% 0.20/0.41  fof(c_0_37, plain, ![X28, X29, X30, X31]:((~v5_pre_topc(X30,X28,X29)|v5_pre_topc(X31,X28,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))|X30!=X31|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X28),u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29))))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))))))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29)))))|(~v2_pre_topc(X29)|~l1_pre_topc(X29))|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))&(~v5_pre_topc(X31,X28,g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))|v5_pre_topc(X30,X28,X29)|X30!=X31|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X28),u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29))))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(g1_pre_topc(u1_struct_0(X29),u1_pre_topc(X29)))))))|(~v1_funct_1(X30)|~v1_funct_2(X30,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X30,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29)))))|(~v2_pre_topc(X29)|~l1_pre_topc(X29))|(~v2_pre_topc(X28)|~l1_pre_topc(X28)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t63_pre_topc])])])])).
% 0.20/0.41  cnf(c_0_38, plain, (v5_pre_topc(X4,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_40, negated_conjecture, (esk6_0=esk7_0), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_41, negated_conjecture, (v1_funct_2(esk7_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_42, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(X1)|~v3_pre_topc(u1_struct_0(X1),X1)|~v2_pre_topc(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35, c_0_36]), c_0_24])])).
% 0.20/0.41  fof(c_0_43, plain, ![X18, X19]:((v1_pre_topc(g1_pre_topc(X18,X19))|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18))))&(l1_pre_topc(g1_pre_topc(X18,X19))|~m1_subset_1(X19,k1_zfmisc_1(k1_zfmisc_1(X18))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_g1_pre_topc])])])).
% 0.20/0.41  fof(c_0_44, plain, ![X20]:(~l1_pre_topc(X20)|m1_subset_1(u1_pre_topc(X20),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X20))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_pre_topc])])).
% 0.20/0.41  cnf(c_0_45, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.41  cnf(c_0_46, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_47, plain, (v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v5_pre_topc(X1,X2,X3)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_38])).
% 0.20/0.41  cnf(c_0_48, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(rw,[status(thm)],[c_0_39, c_0_40])).
% 0.20/0.41  cnf(c_0_49, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(rw,[status(thm)],[c_0_41, c_0_40])).
% 0.20/0.41  cnf(c_0_50, negated_conjecture, (v1_funct_1(esk6_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_51, negated_conjecture, (v2_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_52, negated_conjecture, (l1_pre_topc(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_53, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_19]), c_0_24])]), c_0_31])).
% 0.20/0.41  cnf(c_0_54, plain, (l1_pre_topc(g1_pre_topc(X1,X2))|~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.41  cnf(c_0_55, plain, (m1_subset_1(u1_pre_topc(X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.20/0.41  cnf(c_0_56, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_45])).
% 0.20/0.41  cnf(c_0_57, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_58, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_59, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,esk5_0)|v5_pre_topc(esk7_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_60, negated_conjecture, (~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_46, c_0_40])).
% 0.20/0.41  cnf(c_0_61, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_48]), c_0_49]), c_0_50]), c_0_51]), c_0_52])])).
% 0.20/0.41  cnf(c_0_62, plain, (v5_pre_topc(X4,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|X1!=X4|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.20/0.41  cnf(c_0_63, plain, (u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=u1_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)), inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_54]), c_0_55])).
% 0.20/0.41  cnf(c_0_64, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|~v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_48]), c_0_49]), c_0_50]), c_0_57]), c_0_58])])).
% 0.20/0.41  cnf(c_0_65, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(rw,[status(thm)],[c_0_59, c_0_40])).
% 0.20/0.41  cnf(c_0_66, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(spm,[status(thm)],[c_0_60, c_0_61])).
% 0.20/0.41  cnf(c_0_67, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_68, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk5_0))))), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.41  cnf(c_0_69, plain, (v5_pre_topc(X1,X2,g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3)))|~v5_pre_topc(X1,X2,X3)|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_62])).
% 0.20/0.41  cnf(c_0_70, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_63]), c_0_51]), c_0_52])])).
% 0.20/0.41  cnf(c_0_71, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(esk4_0),u1_struct_0(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_63]), c_0_51]), c_0_52])])).
% 0.20/0.41  cnf(c_0_72, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_64, c_0_65])).
% 0.20/0.41  cnf(c_0_73, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_63]), c_0_67]), c_0_68]), c_0_57]), c_0_58])])).
% 0.20/0.41  cnf(c_0_74, negated_conjecture, (v5_pre_topc(esk6_0,esk4_0,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_67]), c_0_50]), c_0_57]), c_0_51]), c_0_58]), c_0_52]), c_0_68])])).
% 0.20/0.41  cnf(c_0_75, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_32]), c_0_51]), c_0_52])])).
% 0.20/0.41  cnf(c_0_76, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v2_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(spm,[status(thm)],[c_0_73, c_0_74])).
% 0.20/0.41  cnf(c_0_77, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))|~m1_subset_1(u1_pre_topc(esk4_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk4_0))))), inference(spm,[status(thm)],[c_0_75, c_0_54])).
% 0.20/0.41  cnf(c_0_78, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~l1_pre_topc(g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76, c_0_32]), c_0_57]), c_0_58])])).
% 0.20/0.41  cnf(c_0_79, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|v5_pre_topc(esk6_0,esk4_0,esk5_0)|~v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))|~m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_55]), c_0_52])])).
% 0.20/0.41  cnf(c_0_80, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,esk5_0)|~m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(esk5_0))))), inference(spm,[status(thm)],[c_0_78, c_0_54])).
% 0.20/0.41  cnf(c_0_81, plain, (v5_pre_topc(X4,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|X4!=X1|~v1_funct_1(X1)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))|~v2_pre_topc(X3)|~l1_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_33])).
% 0.20/0.41  cnf(c_0_82, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)|v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_63]), c_0_67]), c_0_68]), c_0_51]), c_0_52])])).
% 0.20/0.41  cnf(c_0_83, negated_conjecture, (~v5_pre_topc(esk6_0,esk4_0,esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80, c_0_55]), c_0_58])])).
% 0.20/0.41  cnf(c_0_84, plain, (v5_pre_topc(X1,X2,X3)|~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)),X3)|~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))|~v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))|~v1_funct_1(X1)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))),u1_struct_0(X3))))|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))), inference(er,[status(thm)],[c_0_81])).
% 0.20/0.41  cnf(c_0_85, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48, c_0_63]), c_0_57]), c_0_58])])).
% 0.20/0.41  cnf(c_0_86, negated_conjecture, (v1_funct_2(esk6_0,u1_struct_0(g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0))),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_63]), c_0_57]), c_0_58])])).
% 0.20/0.41  cnf(c_0_87, negated_conjecture, (v5_pre_topc(esk6_0,g1_pre_topc(u1_struct_0(esk4_0),u1_pre_topc(esk4_0)),esk5_0)), inference(sr,[status(thm)],[c_0_82, c_0_83])).
% 0.20/0.41  cnf(c_0_88, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_86]), c_0_67]), c_0_50]), c_0_57]), c_0_51]), c_0_58]), c_0_52]), c_0_68])]), c_0_87])]), c_0_83]), ['proof']).
% 0.20/0.41  # SZS output end CNFRefutation
% 0.20/0.41  # Proof object total steps             : 89
% 0.20/0.41  # Proof object clause steps            : 66
% 0.20/0.41  # Proof object formula steps           : 23
% 0.20/0.41  # Proof object conjectures             : 39
% 0.20/0.41  # Proof object clause conjectures      : 36
% 0.20/0.41  # Proof object formula conjectures     : 3
% 0.20/0.41  # Proof object initial clauses used    : 27
% 0.20/0.41  # Proof object initial formulas used   : 11
% 0.20/0.41  # Proof object generating inferences   : 29
% 0.20/0.41  # Proof object simplifying inferences  : 80
% 0.20/0.41  # Training examples: 0 positive, 0 negative
% 0.20/0.41  # Parsed axioms                        : 11
% 0.20/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.41  # Initial clauses                      : 51
% 0.20/0.41  # Removed in clause preprocessing      : 0
% 0.20/0.41  # Initial clauses in saturation        : 51
% 0.20/0.41  # Processed clauses                    : 110
% 0.20/0.41  # ...of these trivial                  : 2
% 0.20/0.41  # ...subsumed                          : 2
% 0.20/0.41  # ...remaining for further processing  : 105
% 0.20/0.41  # Other redundant clauses eliminated   : 6
% 0.20/0.41  # Clauses deleted for lack of memory   : 0
% 0.20/0.41  # Backward-subsumed                    : 13
% 0.20/0.41  # Backward-rewritten                   : 9
% 0.20/0.41  # Generated clauses                    : 194
% 0.20/0.41  # ...of the previous two non-trivial   : 167
% 0.20/0.41  # Contextual simplify-reflections      : 4
% 0.20/0.41  # Paramodulations                      : 186
% 0.20/0.41  # Factorizations                       : 0
% 0.20/0.41  # Equation resolutions                 : 6
% 0.20/0.41  # Propositional unsat checks           : 0
% 0.20/0.41  #    Propositional check models        : 0
% 0.20/0.41  #    Propositional check unsatisfiable : 0
% 0.20/0.41  #    Propositional clauses             : 0
% 0.20/0.41  #    Propositional clauses after purity: 0
% 0.20/0.41  #    Propositional unsat core size     : 0
% 0.20/0.41  #    Propositional preprocessing time  : 0.000
% 0.20/0.41  #    Propositional encoding time       : 0.000
% 0.20/0.41  #    Propositional solver time         : 0.000
% 0.20/0.41  #    Success case prop preproc time    : 0.000
% 0.20/0.41  #    Success case prop encoding time   : 0.000
% 0.20/0.41  #    Success case prop solver time     : 0.000
% 0.20/0.41  # Current number of processed clauses  : 75
% 0.20/0.41  #    Positive orientable unit clauses  : 18
% 0.20/0.41  #    Positive unorientable unit clauses: 0
% 0.20/0.41  #    Negative unit clauses             : 1
% 0.20/0.41  #    Non-unit-clauses                  : 56
% 0.20/0.41  # Current number of unprocessed clauses: 108
% 0.20/0.41  # ...number of literals in the above   : 855
% 0.20/0.41  # Current number of archived formulas  : 0
% 0.20/0.41  # Current number of archived clauses   : 24
% 0.20/0.41  # Clause-clause subsumption calls (NU) : 2969
% 0.20/0.41  # Rec. Clause-clause subsumption calls : 146
% 0.20/0.41  # Non-unit clause-clause subsumptions  : 18
% 0.20/0.41  # Unit Clause-clause subsumption calls : 56
% 0.20/0.41  # Rewrite failures with RHS unbound    : 0
% 0.20/0.41  # BW rewrite match attempts            : 32
% 0.20/0.41  # BW rewrite match successes           : 5
% 0.20/0.41  # Condensation attempts                : 0
% 0.20/0.41  # Condensation successes               : 0
% 0.20/0.41  # Termbank termtop insertions          : 14074
% 0.20/0.41  
% 0.20/0.41  # -------------------------------------------------
% 0.20/0.41  # User time                : 0.059 s
% 0.20/0.41  # System time              : 0.005 s
% 0.20/0.41  # Total time               : 0.064 s
% 0.20/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
