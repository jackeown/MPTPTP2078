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
% DateTime   : Thu Dec  3 11:17:40 EST 2020

% Result     : Theorem 0.12s
% Output     : CNFRefutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 244 expanded)
%              Number of clauses        :   41 (  77 expanded)
%              Number of leaves         :   10 (  60 expanded)
%              Depth                    :   11
%              Number of atoms          :  334 (2571 expanded)
%              Number of equality atoms :   27 (  39 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal clause size      :   36 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t78_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tmap_1)).

fof(d4_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

fof(t38_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r1_tarski(X3,X1)
       => ( ( X2 = k1_xboole_0
            & X1 != k1_xboole_0 )
          | ( v1_funct_1(k2_partfun1(X1,X2,X4,X3))
            & v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2)
            & m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_funct_2)).

fof(t77_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X1) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X6] :
                          ( ( v1_funct_1(X6)
                            & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                            & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                         => ( ( r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X6,k2_tmap_1(X1,X2,X5,X3))
                              & m1_pre_topc(X4,X3) )
                           => r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X6),k2_tmap_1(X1,X2,X5,X4)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tmap_1)).

fof(redefinition_r2_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & v1_funct_2(X4,X1,X2)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( r2_funct_2(X1,X2,X3,X4)
      <=> X3 = X4 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(t35_borsuk_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => r1_tarski(u1_struct_0(X2),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(dt_k2_partfun1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( v1_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
        & m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(c_0_10,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v2_pre_topc(X2)
              & l1_pre_topc(X2) )
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ! [X4] :
                    ( ( ~ v2_struct_0(X4)
                      & m1_pre_topc(X4,X1) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                       => ( m1_pre_topc(X3,X4)
                         => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t78_tmap_1])).

fof(c_0_11,plain,(
    ! [X21,X22,X23,X24] :
      ( v2_struct_0(X21)
      | ~ v2_pre_topc(X21)
      | ~ l1_pre_topc(X21)
      | v2_struct_0(X22)
      | ~ v2_pre_topc(X22)
      | ~ l1_pre_topc(X22)
      | ~ v1_funct_1(X23)
      | ~ v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))
      | ~ m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))
      | ~ m1_pre_topc(X24,X21)
      | k2_tmap_1(X21,X22,X23,X24) = k2_partfun1(u1_struct_0(X21),u1_struct_0(X22),X23,u1_struct_0(X24)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & m1_pre_topc(esk3_0,esk1_0)
    & ~ v2_struct_0(esk4_0)
    & m1_pre_topc(esk4_0,esk1_0)
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & m1_pre_topc(esk3_0,esk4_0)
    & ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X15,X16,X17,X18] :
      ( ( v1_funct_1(k2_partfun1(X15,X16,X18,X17))
        | X16 = k1_xboole_0
        | ~ r1_tarski(X17,X15)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v1_funct_2(k2_partfun1(X15,X16,X18,X17),X17,X16)
        | X16 = k1_xboole_0
        | ~ r1_tarski(X17,X15)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( m1_subset_1(k2_partfun1(X15,X16,X18,X17),k1_zfmisc_1(k2_zfmisc_1(X17,X16)))
        | X16 = k1_xboole_0
        | ~ r1_tarski(X17,X15)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v1_funct_1(k2_partfun1(X15,X16,X18,X17))
        | X15 != k1_xboole_0
        | ~ r1_tarski(X17,X15)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( v1_funct_2(k2_partfun1(X15,X16,X18,X17),X17,X16)
        | X15 != k1_xboole_0
        | ~ r1_tarski(X17,X15)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) )
      & ( m1_subset_1(k2_partfun1(X15,X16,X18,X17),k1_zfmisc_1(k2_zfmisc_1(X17,X16)))
        | X15 != k1_xboole_0
        | ~ r1_tarski(X17,X15)
        | ~ v1_funct_1(X18)
        | ~ v1_funct_2(X18,X15,X16)
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_2])])])).

fof(c_0_14,plain,(
    ! [X27,X28,X29,X30,X31,X32] :
      ( v2_struct_0(X27)
      | ~ v2_pre_topc(X27)
      | ~ l1_pre_topc(X27)
      | v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | v2_struct_0(X29)
      | ~ m1_pre_topc(X29,X27)
      | v2_struct_0(X30)
      | ~ m1_pre_topc(X30,X27)
      | ~ v1_funct_1(X31)
      | ~ v1_funct_2(X31,u1_struct_0(X27),u1_struct_0(X28))
      | ~ m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,u1_struct_0(X29),u1_struct_0(X28))
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X28))))
      | ~ r2_funct_2(u1_struct_0(X29),u1_struct_0(X28),X32,k2_tmap_1(X27,X28,X31,X29))
      | ~ m1_pre_topc(X30,X29)
      | r2_funct_2(u1_struct_0(X30),u1_struct_0(X28),k3_tmap_1(X27,X28,X29,X30,X32),k2_tmap_1(X27,X28,X31,X30)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_tmap_1])])])])).

cnf(c_0_15,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k2_tmap_1(X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_25,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ r2_funct_2(X11,X12,X13,X14)
        | X13 = X14
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( X13 != X14
        | r2_funct_2(X11,X12,X13,X14)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X11,X12)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | X2 = k1_xboole_0
    | ~ r1_tarski(X4,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_27,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X25)
      | r1_tarski(u1_struct_0(X26),u1_struct_0(X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).

cnf(c_0_28,plain,
    ( v1_funct_2(k2_partfun1(X1,X2,X3,X4),X4,X2)
    | X2 = k1_xboole_0
    | ~ r1_tarski(X4,X1)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X6),k2_tmap_1(X1,X2,X5,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X6,k2_tmap_1(X1,X2,X5,X3))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_30,negated_conjecture,
    ( k2_tmap_1(esk1_0,esk2_0,esk5_0,X1) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_31,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_16]),c_0_21]),c_0_22])])).

cnf(c_0_33,plain,
    ( r1_tarski(u1_struct_0(X2),u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_funct_2(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,X1),X1,u1_struct_0(esk2_0))
    | ~ r1_tarski(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_16]),c_0_21]),c_0_22])])).

cnf(c_0_35,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_funct_2(u1_struct_0(X2),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,X1,X2,X3),k2_tmap_1(esk1_0,esk2_0,esk5_0,X2))
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,X1)
    | ~ r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X3,k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(X3) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_17]),c_0_18]),c_0_19]),c_0_20]),c_0_21]),c_0_16]),c_0_22])]),c_0_23]),c_0_24])).

cnf(c_0_36,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_31])).

cnf(c_0_37,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_20])])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_39,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_funct_2(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_33]),c_0_20])])).

cnf(c_0_40,negated_conjecture,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,X2,X1,k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(X1,X2)
    | ~ v1_funct_2(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2)),u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ m1_subset_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ v1_funct_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_41,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

cnf(c_0_42,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_43,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_funct_2(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_38])).

fof(c_0_44,plain,(
    ! [X7,X8,X9,X10] :
      ( ( v1_funct_1(k2_partfun1(X7,X8,X9,X10))
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) )
      & ( m1_subset_1(k2_partfun1(X7,X8,X9,X10),k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).

cnf(c_0_45,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ v1_funct_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_38])]),c_0_42]),c_0_43])).

cnf(c_0_46,plain,
    ( v1_funct_1(k2_partfun1(X1,X2,X3,X4))
    | ~ v1_funct_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_47,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_48,plain,(
    ! [X20] :
      ( v2_struct_0(X20)
      | ~ l1_struct_0(X20)
      | ~ v1_xboole_0(u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_49,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v2_struct_0(X1)
    | r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ m1_pre_topc(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_16]),c_0_22])])).

cnf(c_0_50,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_51,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_52,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_53,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_30]),c_0_38])])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_51])]),c_0_52]),c_0_53])).

cnf(c_0_56,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

fof(c_0_57,plain,(
    ! [X19] :
      ( ~ l1_pre_topc(X19)
      | l1_struct_0(X19) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_58,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])]),c_0_23])).

cnf(c_0_59,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_60,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_19])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 17:45:57 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  # Version: 2.5pre002
% 0.12/0.33  # No SInE strategy applied
% 0.12/0.33  # Trying AutoSched0 for 299 seconds
% 0.12/0.34  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.12/0.34  # and selection function PSelectComplexExceptRRHorn.
% 0.12/0.34  #
% 0.12/0.34  # Preprocessing time       : 0.014 s
% 0.12/0.34  # Presaturation interreduction done
% 0.12/0.34  
% 0.12/0.34  # Proof found!
% 0.12/0.34  # SZS status Theorem
% 0.12/0.34  # SZS output start CNFRefutation
% 0.12/0.34  fof(t78_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_tmap_1)).
% 0.12/0.34  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.12/0.34  fof(t38_funct_2, axiom, ![X1, X2, X3, X4]:(((v1_funct_1(X4)&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r1_tarski(X3,X1)=>((X2=k1_xboole_0&X1!=k1_xboole_0)|((v1_funct_1(k2_partfun1(X1,X2,X4,X3))&v1_funct_2(k2_partfun1(X1,X2,X4,X3),X3,X2))&m1_subset_1(k2_partfun1(X1,X2,X4,X3),k1_zfmisc_1(k2_zfmisc_1(X3,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_funct_2)).
% 0.12/0.34  fof(t77_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X6,k2_tmap_1(X1,X2,X5,X3))&m1_pre_topc(X4,X3))=>r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X6),k2_tmap_1(X1,X2,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_tmap_1)).
% 0.12/0.34  fof(redefinition_r2_funct_2, axiom, ![X1, X2, X3, X4]:((((((v1_funct_1(X3)&v1_funct_2(X3,X1,X2))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))&v1_funct_1(X4))&v1_funct_2(X4,X1,X2))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(r2_funct_2(X1,X2,X3,X4)<=>X3=X4)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_funct_2)).
% 0.12/0.34  fof(t35_borsuk_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>r1_tarski(u1_struct_0(X2),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 0.12/0.34  fof(dt_k2_partfun1, axiom, ![X1, X2, X3, X4]:((v1_funct_1(X3)&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))=>(v1_funct_1(k2_partfun1(X1,X2,X3,X4))&m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 0.12/0.34  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.12/0.34  fof(fc1_xboole_0, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 0.12/0.34  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.12/0.34  fof(c_0_10, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))))))))), inference(assume_negation,[status(cth)],[t78_tmap_1])).
% 0.12/0.34  fof(c_0_11, plain, ![X21, X22, X23, X24]:(v2_struct_0(X21)|~v2_pre_topc(X21)|~l1_pre_topc(X21)|(v2_struct_0(X22)|~v2_pre_topc(X22)|~l1_pre_topc(X22)|(~v1_funct_1(X23)|~v1_funct_2(X23,u1_struct_0(X21),u1_struct_0(X22))|~m1_subset_1(X23,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X21),u1_struct_0(X22))))|(~m1_pre_topc(X24,X21)|k2_tmap_1(X21,X22,X23,X24)=k2_partfun1(u1_struct_0(X21),u1_struct_0(X22),X23,u1_struct_0(X24)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.12/0.34  fof(c_0_12, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(m1_pre_topc(esk3_0,esk4_0)&~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).
% 0.12/0.34  fof(c_0_13, plain, ![X15, X16, X17, X18]:((((v1_funct_1(k2_partfun1(X15,X16,X18,X17))|X16=k1_xboole_0|~r1_tarski(X17,X15)|(~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))&(v1_funct_2(k2_partfun1(X15,X16,X18,X17),X17,X16)|X16=k1_xboole_0|~r1_tarski(X17,X15)|(~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))))&(m1_subset_1(k2_partfun1(X15,X16,X18,X17),k1_zfmisc_1(k2_zfmisc_1(X17,X16)))|X16=k1_xboole_0|~r1_tarski(X17,X15)|(~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))))&(((v1_funct_1(k2_partfun1(X15,X16,X18,X17))|X15!=k1_xboole_0|~r1_tarski(X17,X15)|(~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16)))))&(v1_funct_2(k2_partfun1(X15,X16,X18,X17),X17,X16)|X15!=k1_xboole_0|~r1_tarski(X17,X15)|(~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))))&(m1_subset_1(k2_partfun1(X15,X16,X18,X17),k1_zfmisc_1(k2_zfmisc_1(X17,X16)))|X15!=k1_xboole_0|~r1_tarski(X17,X15)|(~v1_funct_1(X18)|~v1_funct_2(X18,X15,X16)|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X15,X16))))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t38_funct_2])])])).
% 0.12/0.34  fof(c_0_14, plain, ![X27, X28, X29, X30, X31, X32]:(v2_struct_0(X27)|~v2_pre_topc(X27)|~l1_pre_topc(X27)|(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|(v2_struct_0(X29)|~m1_pre_topc(X29,X27)|(v2_struct_0(X30)|~m1_pre_topc(X30,X27)|(~v1_funct_1(X31)|~v1_funct_2(X31,u1_struct_0(X27),u1_struct_0(X28))|~m1_subset_1(X31,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X27),u1_struct_0(X28))))|(~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X29),u1_struct_0(X28))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X29),u1_struct_0(X28))))|(~r2_funct_2(u1_struct_0(X29),u1_struct_0(X28),X32,k2_tmap_1(X27,X28,X31,X29))|~m1_pre_topc(X30,X29)|r2_funct_2(u1_struct_0(X30),u1_struct_0(X28),k3_tmap_1(X27,X28,X29,X30,X32),k2_tmap_1(X27,X28,X31,X30))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_tmap_1])])])])).
% 0.12/0.34  cnf(c_0_15, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.12/0.34  cnf(c_0_16, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  cnf(c_0_17, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  cnf(c_0_18, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  cnf(c_0_19, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  cnf(c_0_20, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  cnf(c_0_21, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  cnf(c_0_22, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  cnf(c_0_23, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  cnf(c_0_24, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.34  fof(c_0_25, plain, ![X11, X12, X13, X14]:((~r2_funct_2(X11,X12,X13,X14)|X13=X14|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))&(X13!=X14|r2_funct_2(X11,X12,X13,X14)|(~v1_funct_1(X13)|~v1_funct_2(X13,X11,X12)|~m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))|~v1_funct_1(X14)|~v1_funct_2(X14,X11,X12)|~m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).
% 0.12/0.35  cnf(c_0_26, plain, (m1_subset_1(k2_partfun1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))|X2=k1_xboole_0|~r1_tarski(X4,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.35  fof(c_0_27, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_pre_topc(X26,X25)|r1_tarski(u1_struct_0(X26),u1_struct_0(X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_borsuk_1])])])).
% 0.12/0.35  cnf(c_0_28, plain, (v1_funct_2(k2_partfun1(X1,X2,X3,X4),X4,X2)|X2=k1_xboole_0|~r1_tarski(X4,X1)|~v1_funct_1(X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.12/0.35  cnf(c_0_29, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X6),k2_tmap_1(X1,X2,X5,X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X6,k2_tmap_1(X1,X2,X5,X3))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.12/0.35  cnf(c_0_30, negated_conjecture, (k2_tmap_1(esk1_0,esk2_0,esk5_0,X1)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1))|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15, c_0_16]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_22])]), c_0_23]), c_0_24])).
% 0.12/0.35  cnf(c_0_31, plain, (r2_funct_2(X3,X4,X1,X2)|X1!=X2|~v1_funct_1(X1)|~v1_funct_2(X1,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))|~v1_funct_1(X2)|~v1_funct_2(X2,X3,X4)|~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.12/0.35  cnf(c_0_32, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,X1),k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))|~r1_tarski(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_16]), c_0_21]), c_0_22])])).
% 0.12/0.35  cnf(c_0_33, plain, (r1_tarski(u1_struct_0(X2),u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.12/0.35  cnf(c_0_34, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v1_funct_2(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,X1),X1,u1_struct_0(esk2_0))|~r1_tarski(X1,u1_struct_0(esk1_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_16]), c_0_21]), c_0_22])])).
% 0.12/0.35  cnf(c_0_35, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|r2_funct_2(u1_struct_0(X2),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,X1,X2,X3),k2_tmap_1(esk1_0,esk2_0,esk5_0,X2))|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,X1)|~r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X3,k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)))|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~v1_funct_1(X3)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_17]), c_0_18]), c_0_19]), c_0_20]), c_0_21]), c_0_16]), c_0_22])]), c_0_23]), c_0_24])).
% 0.12/0.35  cnf(c_0_36, plain, (r2_funct_2(X1,X2,X3,X3)|~v1_funct_2(X3,X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))|~v1_funct_1(X3)), inference(er,[status(thm)],[c_0_31])).
% 0.12/0.35  cnf(c_0_37, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32, c_0_33]), c_0_20])])).
% 0.12/0.35  cnf(c_0_38, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_39, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v1_funct_2(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X1)),u1_struct_0(X1),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_33]), c_0_20])])).
% 0.12/0.35  cnf(c_0_40, negated_conjecture, (v2_struct_0(X1)|v2_struct_0(X2)|r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,X2,X1,k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(X1,X2)|~v1_funct_2(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2)),u1_struct_0(X2),u1_struct_0(esk2_0))|~m1_subset_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))|~v1_funct_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2)))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.12/0.35  cnf(c_0_41, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|m1_subset_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.12/0.35  cnf(c_0_42, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_43, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v1_funct_2(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0),u1_struct_0(esk2_0))), inference(spm,[status(thm)],[c_0_39, c_0_38])).
% 0.12/0.35  fof(c_0_44, plain, ![X7, X8, X9, X10]:((v1_funct_1(k2_partfun1(X7,X8,X9,X10))|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))&(m1_subset_1(k2_partfun1(X7,X8,X9,X10),k1_zfmisc_1(k2_zfmisc_1(X7,X8)))|(~v1_funct_1(X9)|~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_partfun1])])])).
% 0.12/0.35  cnf(c_0_45, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v2_struct_0(X1)|r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)|~v1_funct_1(k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_38])]), c_0_42]), c_0_43])).
% 0.12/0.35  cnf(c_0_46, plain, (v1_funct_1(k2_partfun1(X1,X2,X3,X4))|~v1_funct_1(X3)|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))), inference(split_conjunct,[status(thm)],[c_0_44])).
% 0.12/0.35  cnf(c_0_47, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  fof(c_0_48, plain, ![X20]:(v2_struct_0(X20)|~l1_struct_0(X20)|~v1_xboole_0(u1_struct_0(X20))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.12/0.35  cnf(c_0_49, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0|v2_struct_0(X1)|r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|~m1_pre_topc(X1,esk1_0)|~m1_pre_topc(X1,esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_46]), c_0_16]), c_0_22])])).
% 0.12/0.35  cnf(c_0_50, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_51, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_52, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.12/0.35  cnf(c_0_53, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_30]), c_0_38])])).
% 0.12/0.35  cnf(c_0_54, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.12/0.35  cnf(c_0_55, negated_conjecture, (u1_struct_0(esk2_0)=k1_xboole_0), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_51])]), c_0_52]), c_0_53])).
% 0.12/0.35  cnf(c_0_56, plain, (v1_xboole_0(k1_xboole_0)), inference(split_conjunct,[status(thm)],[fc1_xboole_0])).
% 0.12/0.35  fof(c_0_57, plain, ![X19]:(~l1_pre_topc(X19)|l1_struct_0(X19)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.12/0.35  cnf(c_0_58, negated_conjecture, (~l1_struct_0(esk2_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_55]), c_0_56])]), c_0_23])).
% 0.12/0.35  cnf(c_0_59, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_57])).
% 0.12/0.35  cnf(c_0_60, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_19])]), ['proof']).
% 0.12/0.35  # SZS output end CNFRefutation
% 0.12/0.35  # Proof object total steps             : 61
% 0.12/0.35  # Proof object clause steps            : 41
% 0.12/0.35  # Proof object formula steps           : 20
% 0.12/0.35  # Proof object conjectures             : 33
% 0.12/0.35  # Proof object clause conjectures      : 30
% 0.12/0.35  # Proof object formula conjectures     : 3
% 0.12/0.35  # Proof object initial clauses used    : 25
% 0.12/0.35  # Proof object initial formulas used   : 10
% 0.12/0.35  # Proof object generating inferences   : 15
% 0.12/0.35  # Proof object simplifying inferences  : 48
% 0.12/0.35  # Training examples: 0 positive, 0 negative
% 0.12/0.35  # Parsed axioms                        : 10
% 0.12/0.35  # Removed by relevancy pruning/SinE    : 0
% 0.12/0.35  # Initial clauses                      : 31
% 0.12/0.35  # Removed in clause preprocessing      : 0
% 0.12/0.35  # Initial clauses in saturation        : 31
% 0.12/0.35  # Processed clauses                    : 99
% 0.12/0.35  # ...of these trivial                  : 0
% 0.12/0.35  # ...subsumed                          : 4
% 0.12/0.35  # ...remaining for further processing  : 95
% 0.12/0.35  # Other redundant clauses eliminated   : 1
% 0.12/0.35  # Clauses deleted for lack of memory   : 0
% 0.12/0.35  # Backward-subsumed                    : 4
% 0.12/0.35  # Backward-rewritten                   : 31
% 0.12/0.35  # Generated clauses                    : 67
% 0.12/0.35  # ...of the previous two non-trivial   : 80
% 0.12/0.35  # Contextual simplify-reflections      : 9
% 0.12/0.35  # Paramodulations                      : 66
% 0.12/0.35  # Factorizations                       : 0
% 0.12/0.35  # Equation resolutions                 : 1
% 0.12/0.35  # Propositional unsat checks           : 0
% 0.12/0.35  #    Propositional check models        : 0
% 0.12/0.35  #    Propositional check unsatisfiable : 0
% 0.12/0.35  #    Propositional clauses             : 0
% 0.12/0.35  #    Propositional clauses after purity: 0
% 0.12/0.35  #    Propositional unsat core size     : 0
% 0.12/0.35  #    Propositional preprocessing time  : 0.000
% 0.12/0.35  #    Propositional encoding time       : 0.000
% 0.12/0.35  #    Propositional solver time         : 0.000
% 0.12/0.35  #    Success case prop preproc time    : 0.000
% 0.12/0.35  #    Success case prop encoding time   : 0.000
% 0.12/0.35  #    Success case prop solver time     : 0.000
% 0.12/0.35  # Current number of processed clauses  : 30
% 0.12/0.35  #    Positive orientable unit clauses  : 10
% 0.12/0.35  #    Positive unorientable unit clauses: 0
% 0.12/0.35  #    Negative unit clauses             : 5
% 0.12/0.35  #    Non-unit-clauses                  : 15
% 0.12/0.35  # Current number of unprocessed clauses: 41
% 0.12/0.35  # ...number of literals in the above   : 308
% 0.12/0.35  # Current number of archived formulas  : 0
% 0.12/0.35  # Current number of archived clauses   : 64
% 0.12/0.35  # Clause-clause subsumption calls (NU) : 1648
% 0.12/0.35  # Rec. Clause-clause subsumption calls : 73
% 0.12/0.35  # Non-unit clause-clause subsumptions  : 16
% 0.12/0.35  # Unit Clause-clause subsumption calls : 19
% 0.12/0.35  # Rewrite failures with RHS unbound    : 0
% 0.12/0.35  # BW rewrite match attempts            : 1
% 0.12/0.35  # BW rewrite match successes           : 1
% 0.12/0.35  # Condensation attempts                : 0
% 0.12/0.35  # Condensation successes               : 0
% 0.12/0.35  # Termbank termtop insertions          : 7619
% 0.12/0.35  
% 0.12/0.35  # -------------------------------------------------
% 0.12/0.35  # User time                : 0.018 s
% 0.12/0.35  # System time              : 0.004 s
% 0.12/0.35  # Total time               : 0.022 s
% 0.12/0.35  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
