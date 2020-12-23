%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:17:40 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 497 expanded)
%              Number of clauses        :   53 ( 154 expanded)
%              Number of leaves         :    9 ( 123 expanded)
%              Depth                    :   26
%              Number of atoms          :  422 (5106 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :   26 (   7 average)
%              Maximal clause size      :   21 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_tmap_1)).

fof(d5_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ! [X4] :
                  ( m1_pre_topc(X4,X1)
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X4,X3)
                       => k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(t2_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => m1_pre_topc(X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

fof(t74_tmap_1,axiom,(
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
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                 => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_tmap_1)).

fof(dt_k2_tmap_1,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X2)
        & v1_funct_1(X3)
        & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
        & l1_struct_0(X4) )
     => ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
        & v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
        & m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tmap_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(c_0_9,negated_conjecture,(
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

fof(c_0_10,plain,(
    ! [X14,X15,X16,X17,X18] :
      ( v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | v2_struct_0(X15)
      | ~ v2_pre_topc(X15)
      | ~ l1_pre_topc(X15)
      | ~ m1_pre_topc(X16,X14)
      | ~ m1_pre_topc(X17,X14)
      | ~ v1_funct_1(X18)
      | ~ v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X15))
      | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X15))))
      | ~ m1_pre_topc(X17,X16)
      | k3_tmap_1(X14,X15,X16,X17,X18) = k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),X18,u1_struct_0(X17)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_11,negated_conjecture,
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
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).

cnf(c_0_12,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_tmap_1(X1,X2,X3,X4,X5) = k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ m1_pre_topc(X4,X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_19,plain,(
    ! [X23] :
      ( ~ l1_pre_topc(X23)
      | m1_pre_topc(X23,X23) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).

cnf(c_0_20,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(X2,esk1_0)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12,c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17])]),c_0_18])).

cnf(c_0_21,plain,
    ( m1_pre_topc(X1,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X10,X11,X12,X13] :
      ( v2_struct_0(X10)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | v2_struct_0(X11)
      | ~ v2_pre_topc(X11)
      | ~ l1_pre_topc(X11)
      | ~ v1_funct_1(X12)
      | ~ v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))
      | ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))
      | ~ m1_pre_topc(X13,X10)
      | k2_tmap_1(X10,X11,X12,X13) = k2_partfun1(u1_struct_0(X10),u1_struct_0(X11),X12,u1_struct_0(X13)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).

cnf(c_0_24,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk1_0,esk5_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk1_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_25,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_27,plain,(
    ! [X24,X25,X26,X27] :
      ( v2_struct_0(X24)
      | ~ v2_pre_topc(X24)
      | ~ l1_pre_topc(X24)
      | v2_struct_0(X25)
      | ~ v2_pre_topc(X25)
      | ~ l1_pre_topc(X25)
      | v2_struct_0(X26)
      | ~ m1_pre_topc(X26,X24)
      | ~ v1_funct_1(X27)
      | ~ v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))
      | ~ m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))
      | r2_funct_2(u1_struct_0(X26),u1_struct_0(X25),X27,k3_tmap_1(X24,X25,X26,X26,X27)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).

cnf(c_0_28,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk1_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_25]),c_0_22])]),c_0_26])).

fof(c_0_30,plain,(
    ! [X28,X29,X30,X31,X32,X33] :
      ( v2_struct_0(X28)
      | ~ v2_pre_topc(X28)
      | ~ l1_pre_topc(X28)
      | v2_struct_0(X29)
      | ~ v2_pre_topc(X29)
      | ~ l1_pre_topc(X29)
      | v2_struct_0(X30)
      | ~ m1_pre_topc(X30,X28)
      | v2_struct_0(X31)
      | ~ m1_pre_topc(X31,X28)
      | ~ v1_funct_1(X32)
      | ~ v1_funct_2(X32,u1_struct_0(X28),u1_struct_0(X29))
      | ~ m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))
      | ~ v1_funct_1(X33)
      | ~ v1_funct_2(X33,u1_struct_0(X30),u1_struct_0(X29))
      | ~ m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))
      | ~ r2_funct_2(u1_struct_0(X30),u1_struct_0(X29),X33,k2_tmap_1(X28,X29,X32,X30))
      | ~ m1_pre_topc(X31,X30)
      | r2_funct_2(u1_struct_0(X31),u1_struct_0(X29),k3_tmap_1(X28,X29,X30,X31,X33),k2_tmap_1(X28,X29,X32,X31)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_tmap_1])])])])).

cnf(c_0_31,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ m1_pre_topc(X3,X1)
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk1_0)
    | ~ m1_pre_topc(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_25]),c_0_17]),c_0_22])]),c_0_18]),c_0_26])).

cnf(c_0_33,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_34,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk1_0))
    | ~ m1_pre_topc(esk1_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_25]),c_0_17]),c_0_22])]),c_0_26]),c_0_18])).

cnf(c_0_35,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_36,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(esk1_0,esk1_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_25]),c_0_17]),c_0_22])]),c_0_26]),c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk5_0) = k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ m1_pre_topc(esk1_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_20,c_0_35])).

cnf(c_0_38,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_21]),c_0_22])])).

cnf(c_0_39,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_40,negated_conjecture,
    ( k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0)) = k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_21]),c_0_25]),c_0_35]),c_0_22])]),c_0_26])).

cnf(c_0_41,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_35]),c_0_39])).

cnf(c_0_42,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0) = k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_40]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_25]),c_0_35]),c_0_17]),c_0_22])]),c_0_18]),c_0_26])).

fof(c_0_43,plain,(
    ! [X19,X20,X21,X22] :
      ( ( v1_funct_1(k2_tmap_1(X19,X20,X21,X22))
        | ~ l1_struct_0(X19)
        | ~ l1_struct_0(X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_struct_0(X22) )
      & ( v1_funct_2(k2_tmap_1(X19,X20,X21,X22),u1_struct_0(X22),u1_struct_0(X20))
        | ~ l1_struct_0(X19)
        | ~ l1_struct_0(X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_struct_0(X22) )
      & ( m1_subset_1(k2_tmap_1(X19,X20,X21,X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20))))
        | ~ l1_struct_0(X19)
        | ~ l1_struct_0(X20)
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | ~ l1_struct_0(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).

cnf(c_0_44,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)) ),
    inference(rw,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_45,plain,
    ( v1_funct_1(k2_tmap_1(X1,X2,X3,X4))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_46,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_44]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_25]),c_0_35]),c_0_17]),c_0_22])]),c_0_39]),c_0_18]),c_0_26])).

cnf(c_0_47,negated_conjecture,
    ( v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_13]),c_0_14]),c_0_15])])).

fof(c_0_48,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(X7)
      | l1_struct_0(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_49,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_50,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

fof(c_0_51,plain,(
    ! [X8,X9] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_pre_topc(X9,X8)
      | l1_pre_topc(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

cnf(c_0_52,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_17])])).

cnf(c_0_53,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_54,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_50]),c_0_22])])).

cnf(c_0_55,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_35]),c_0_22])])).

cnf(c_0_56,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_50]),c_0_55])])).

cnf(c_0_57,plain,
    ( v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_58,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_59,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_50]),c_0_55])])).

cnf(c_0_60,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_50]),c_0_17])])).

cnf(c_0_61,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_50]),c_0_22])])).

cnf(c_0_62,plain,
    ( m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X4) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_63,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_struct_0(esk4_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_13]),c_0_14]),c_0_15])])).

cnf(c_0_64,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_struct_0(esk2_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_50]),c_0_55])])).

cnf(c_0_65,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_50]),c_0_17])])).

cnf(c_0_66,negated_conjecture,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk4_0)
    | ~ m1_pre_topc(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_50]),c_0_22])])).

cnf(c_0_67,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_68,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_69,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_71,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_67]),c_0_68])]),c_0_69]),c_0_70]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:30:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_AE_CS_SP_PS_S0V
% 0.20/0.39  # and selection function PSelectComplexExceptRRHorn.
% 0.20/0.39  #
% 0.20/0.39  # Preprocessing time       : 0.028 s
% 0.20/0.39  # Presaturation interreduction done
% 0.20/0.39  
% 0.20/0.39  # Proof found!
% 0.20/0.39  # SZS status Theorem
% 0.20/0.39  # SZS output start CNFRefutation
% 0.20/0.39  fof(t78_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_tmap_1)).
% 0.20/0.39  fof(d5_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(m1_pre_topc(X3,X1)=>![X4]:(m1_pre_topc(X4,X1)=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>(m1_pre_topc(X4,X3)=>k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 0.20/0.39  fof(t2_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>m1_pre_topc(X1,X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 0.20/0.39  fof(d4_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X4]:(m1_pre_topc(X4,X1)=>k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 0.20/0.39  fof(t74_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:(((v1_funct_1(X4)&v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_tmap_1)).
% 0.20/0.39  fof(t77_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>![X6]:(((v1_funct_1(X6)&v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2)))&m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))))=>((r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X6,k2_tmap_1(X1,X2,X5,X3))&m1_pre_topc(X4,X3))=>r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X6),k2_tmap_1(X1,X2,X5,X4))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_tmap_1)).
% 0.20/0.39  fof(dt_k2_tmap_1, axiom, ![X1, X2, X3, X4]:((((((l1_struct_0(X1)&l1_struct_0(X2))&v1_funct_1(X3))&v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))&l1_struct_0(X4))=>((v1_funct_1(k2_tmap_1(X1,X2,X3,X4))&v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2)))&m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_tmap_1)).
% 0.20/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.39  fof(c_0_9, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X1))=>![X5]:(((v1_funct_1(X5)&v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2)))&m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))))=>(m1_pre_topc(X3,X4)=>r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,k2_tmap_1(X1,X2,X5,X4)),k2_tmap_1(X1,X2,X5,X3))))))))), inference(assume_negation,[status(cth)],[t78_tmap_1])).
% 0.20/0.39  fof(c_0_10, plain, ![X14, X15, X16, X17, X18]:(v2_struct_0(X14)|~v2_pre_topc(X14)|~l1_pre_topc(X14)|(v2_struct_0(X15)|~v2_pre_topc(X15)|~l1_pre_topc(X15)|(~m1_pre_topc(X16,X14)|(~m1_pre_topc(X17,X14)|(~v1_funct_1(X18)|~v1_funct_2(X18,u1_struct_0(X16),u1_struct_0(X15))|~m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),u1_struct_0(X15))))|(~m1_pre_topc(X17,X16)|k3_tmap_1(X14,X15,X16,X17,X18)=k2_partfun1(u1_struct_0(X16),u1_struct_0(X15),X18,u1_struct_0(X17)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).
% 0.20/0.39  fof(c_0_11, negated_conjecture, (((~v2_struct_0(esk1_0)&v2_pre_topc(esk1_0))&l1_pre_topc(esk1_0))&(((~v2_struct_0(esk2_0)&v2_pre_topc(esk2_0))&l1_pre_topc(esk2_0))&((~v2_struct_0(esk3_0)&m1_pre_topc(esk3_0,esk1_0))&((~v2_struct_0(esk4_0)&m1_pre_topc(esk4_0,esk1_0))&(((v1_funct_1(esk5_0)&v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)))&m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))))&(m1_pre_topc(esk3_0,esk4_0)&~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_9])])])])).
% 0.20/0.39  cnf(c_0_12, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k3_tmap_1(X1,X2,X3,X4,X5)=k2_partfun1(u1_struct_0(X3),u1_struct_0(X2),X5,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_10])).
% 0.20/0.39  cnf(c_0_13, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_14, negated_conjecture, (v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_15, negated_conjecture, (v1_funct_1(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_16, negated_conjecture, (v2_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_17, negated_conjecture, (l1_pre_topc(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_18, negated_conjecture, (~v2_struct_0(esk2_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  fof(c_0_19, plain, ![X23]:(~l1_pre_topc(X23)|m1_pre_topc(X23,X23)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tsep_1])])).
% 0.20/0.39  cnf(c_0_20, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,X2,esk5_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(X2,esk1_0)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_12, c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_17])]), c_0_18])).
% 0.20/0.39  cnf(c_0_21, plain, (m1_pre_topc(X1,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.39  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  fof(c_0_23, plain, ![X10, X11, X12, X13]:(v2_struct_0(X10)|~v2_pre_topc(X10)|~l1_pre_topc(X10)|(v2_struct_0(X11)|~v2_pre_topc(X11)|~l1_pre_topc(X11)|(~v1_funct_1(X12)|~v1_funct_2(X12,u1_struct_0(X10),u1_struct_0(X11))|~m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X10),u1_struct_0(X11))))|(~m1_pre_topc(X13,X10)|k2_tmap_1(X10,X11,X12,X13)=k2_partfun1(u1_struct_0(X10),u1_struct_0(X11),X12,u1_struct_0(X13)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d4_tmap_1])])])])).
% 0.20/0.39  cnf(c_0_24, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk1_0,esk5_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk1_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(esk1_0,X1)|~l1_pre_topc(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])])).
% 0.20/0.39  cnf(c_0_25, negated_conjecture, (v2_pre_topc(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_26, negated_conjecture, (~v2_struct_0(esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  fof(c_0_27, plain, ![X24, X25, X26, X27]:(v2_struct_0(X24)|~v2_pre_topc(X24)|~l1_pre_topc(X24)|(v2_struct_0(X25)|~v2_pre_topc(X25)|~l1_pre_topc(X25)|(v2_struct_0(X26)|~m1_pre_topc(X26,X24)|(~v1_funct_1(X27)|~v1_funct_2(X27,u1_struct_0(X26),u1_struct_0(X25))|~m1_subset_1(X27,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X26),u1_struct_0(X25))))|r2_funct_2(u1_struct_0(X26),u1_struct_0(X25),X27,k3_tmap_1(X24,X25,X26,X26,X27)))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t74_tmap_1])])])])).
% 0.20/0.39  cnf(c_0_28, plain, (v2_struct_0(X1)|v2_struct_0(X2)|k2_tmap_1(X1,X2,X3,X4)=k2_partfun1(u1_struct_0(X1),u1_struct_0(X2),X3,u1_struct_0(X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~m1_pre_topc(X4,X1)), inference(split_conjunct,[status(thm)],[c_0_23])).
% 0.20/0.39  cnf(c_0_29, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk1_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_25]), c_0_22])]), c_0_26])).
% 0.20/0.39  fof(c_0_30, plain, ![X28, X29, X30, X31, X32, X33]:(v2_struct_0(X28)|~v2_pre_topc(X28)|~l1_pre_topc(X28)|(v2_struct_0(X29)|~v2_pre_topc(X29)|~l1_pre_topc(X29)|(v2_struct_0(X30)|~m1_pre_topc(X30,X28)|(v2_struct_0(X31)|~m1_pre_topc(X31,X28)|(~v1_funct_1(X32)|~v1_funct_2(X32,u1_struct_0(X28),u1_struct_0(X29))|~m1_subset_1(X32,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X29))))|(~v1_funct_1(X33)|~v1_funct_2(X33,u1_struct_0(X30),u1_struct_0(X29))|~m1_subset_1(X33,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X30),u1_struct_0(X29))))|(~r2_funct_2(u1_struct_0(X30),u1_struct_0(X29),X33,k2_tmap_1(X28,X29,X32,X30))|~m1_pre_topc(X31,X30)|r2_funct_2(u1_struct_0(X31),u1_struct_0(X29),k3_tmap_1(X28,X29,X30,X31,X33),k2_tmap_1(X28,X29,X32,X31))))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t77_tmap_1])])])])).
% 0.20/0.39  cnf(c_0_31, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X4,k3_tmap_1(X1,X2,X3,X3,X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~v1_funct_1(X4)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.20/0.39  cnf(c_0_32, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk1_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk1_0)|~m1_pre_topc(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_29]), c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_25]), c_0_17]), c_0_22])]), c_0_18]), c_0_26])).
% 0.20/0.39  cnf(c_0_33, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X3)|v2_struct_0(X4)|r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k3_tmap_1(X1,X2,X3,X4,X6),k2_tmap_1(X1,X2,X5,X4))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~m1_pre_topc(X3,X1)|~m1_pre_topc(X4,X1)|~v1_funct_1(X5)|~v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~v1_funct_1(X6)|~v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))|~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),X6,k2_tmap_1(X1,X2,X5,X3))|~m1_pre_topc(X4,X3)), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.20/0.39  cnf(c_0_34, negated_conjecture, (r2_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk1_0))|~m1_pre_topc(esk1_0,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_25]), c_0_17]), c_0_22])]), c_0_26]), c_0_18])).
% 0.20/0.39  cnf(c_0_35, negated_conjecture, (m1_pre_topc(esk4_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_36, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_pre_topc(esk1_0,esk1_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_34]), c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_25]), c_0_17]), c_0_22])]), c_0_26]), c_0_18])).
% 0.20/0.39  cnf(c_0_37, negated_conjecture, (k3_tmap_1(X1,esk2_0,esk1_0,esk4_0,esk5_0)=k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))|v2_struct_0(X1)|~v2_pre_topc(X1)|~m1_pre_topc(esk1_0,X1)|~m1_pre_topc(esk4_0,X1)|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_20, c_0_35])).
% 0.20/0.39  cnf(c_0_38, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,X1,esk5_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36, c_0_21]), c_0_22])])).
% 0.20/0.39  cnf(c_0_39, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_40, negated_conjecture, (k2_partfun1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk4_0))=k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_21]), c_0_25]), c_0_35]), c_0_22])]), c_0_26])).
% 0.20/0.39  cnf(c_0_41, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_38, c_0_35]), c_0_39])).
% 0.20/0.39  cnf(c_0_42, negated_conjecture, (k3_tmap_1(esk1_0,esk2_0,esk1_0,esk4_0,esk5_0)=k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28, c_0_40]), c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_25]), c_0_35]), c_0_17]), c_0_22])]), c_0_18]), c_0_26])).
% 0.20/0.39  fof(c_0_43, plain, ![X19, X20, X21, X22]:(((v1_funct_1(k2_tmap_1(X19,X20,X21,X22))|(~l1_struct_0(X19)|~l1_struct_0(X20)|~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))|~l1_struct_0(X22)))&(v1_funct_2(k2_tmap_1(X19,X20,X21,X22),u1_struct_0(X22),u1_struct_0(X20))|(~l1_struct_0(X19)|~l1_struct_0(X20)|~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))|~l1_struct_0(X22))))&(m1_subset_1(k2_tmap_1(X19,X20,X21,X22),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X22),u1_struct_0(X20))))|(~l1_struct_0(X19)|~l1_struct_0(X20)|~v1_funct_1(X21)|~v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))|~m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))|~l1_struct_0(X22)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_tmap_1])])])).
% 0.20/0.39  cnf(c_0_44, negated_conjecture, (r2_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))), inference(rw,[status(thm)],[c_0_41, c_0_42])).
% 0.20/0.39  cnf(c_0_45, plain, (v1_funct_1(k2_tmap_1(X1,X2,X3,X4))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_46, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0))|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33, c_0_44]), c_0_13]), c_0_14]), c_0_15]), c_0_16]), c_0_25]), c_0_35]), c_0_17]), c_0_22])]), c_0_39]), c_0_18]), c_0_26])).
% 0.20/0.39  cnf(c_0_47, negated_conjecture, (v1_funct_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45, c_0_13]), c_0_14]), c_0_15])])).
% 0.20/0.39  fof(c_0_48, plain, ![X7]:(~l1_pre_topc(X7)|l1_struct_0(X7)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.39  cnf(c_0_49, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk4_0)), inference(spm,[status(thm)],[c_0_46, c_0_47])).
% 0.20/0.39  cnf(c_0_50, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.39  fof(c_0_51, plain, ![X8, X9]:(~l1_pre_topc(X8)|(~m1_pre_topc(X9,X8)|l1_pre_topc(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.39  cnf(c_0_52, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)|~l1_struct_0(esk1_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49, c_0_50]), c_0_17])])).
% 0.20/0.39  cnf(c_0_53, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.20/0.39  cnf(c_0_54, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)|~l1_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52, c_0_50]), c_0_22])])).
% 0.20/0.39  cnf(c_0_55, negated_conjecture, (l1_pre_topc(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53, c_0_35]), c_0_22])])).
% 0.20/0.39  cnf(c_0_56, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~v1_funct_2(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),u1_struct_0(esk4_0),u1_struct_0(esk2_0))|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54, c_0_50]), c_0_55])])).
% 0.20/0.39  cnf(c_0_57, plain, (v1_funct_2(k2_tmap_1(X1,X2,X3,X4),u1_struct_0(X4),u1_struct_0(X2))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_58, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56, c_0_57]), c_0_13]), c_0_14]), c_0_15])])).
% 0.20/0.39  cnf(c_0_59, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_50]), c_0_55])])).
% 0.20/0.39  cnf(c_0_60, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59, c_0_50]), c_0_17])])).
% 0.20/0.39  cnf(c_0_61, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_subset_1(k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60, c_0_50]), c_0_22])])).
% 0.20/0.39  cnf(c_0_62, plain, (m1_subset_1(k2_tmap_1(X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))|~l1_struct_0(X1)|~l1_struct_0(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))|~l1_struct_0(X4)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.39  cnf(c_0_63, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)|~l1_struct_0(esk4_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_13]), c_0_14]), c_0_15])])).
% 0.20/0.39  cnf(c_0_64, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)|~l1_struct_0(esk2_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_50]), c_0_55])])).
% 0.20/0.39  cnf(c_0_65, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)|~l1_struct_0(esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_50]), c_0_17])])).
% 0.20/0.39  cnf(c_0_66, negated_conjecture, (r2_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,X1,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,X1))|v2_struct_0(X1)|~m1_pre_topc(X1,esk4_0)|~m1_pre_topc(X1,esk1_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_50]), c_0_22])])).
% 0.20/0.39  cnf(c_0_67, negated_conjecture, (m1_pre_topc(esk3_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_68, negated_conjecture, (m1_pre_topc(esk3_0,esk1_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_69, negated_conjecture, (~r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,k2_tmap_1(esk1_0,esk2_0,esk5_0,esk4_0)),k2_tmap_1(esk1_0,esk2_0,esk5_0,esk3_0))), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_70, negated_conjecture, (~v2_struct_0(esk3_0)), inference(split_conjunct,[status(thm)],[c_0_11])).
% 0.20/0.39  cnf(c_0_71, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_67]), c_0_68])]), c_0_69]), c_0_70]), ['proof']).
% 0.20/0.39  # SZS output end CNFRefutation
% 0.20/0.39  # Proof object total steps             : 72
% 0.20/0.39  # Proof object clause steps            : 53
% 0.20/0.39  # Proof object formula steps           : 19
% 0.20/0.39  # Proof object conjectures             : 46
% 0.20/0.39  # Proof object clause conjectures      : 43
% 0.20/0.39  # Proof object formula conjectures     : 3
% 0.20/0.39  # Proof object initial clauses used    : 25
% 0.20/0.39  # Proof object initial formulas used   : 9
% 0.20/0.39  # Proof object generating inferences   : 27
% 0.20/0.39  # Proof object simplifying inferences  : 109
% 0.20/0.39  # Training examples: 0 positive, 0 negative
% 0.20/0.39  # Parsed axioms                        : 9
% 0.20/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.39  # Initial clauses                      : 25
% 0.20/0.39  # Removed in clause preprocessing      : 0
% 0.20/0.39  # Initial clauses in saturation        : 25
% 0.20/0.39  # Processed clauses                    : 140
% 0.20/0.39  # ...of these trivial                  : 3
% 0.20/0.39  # ...subsumed                          : 10
% 0.20/0.39  # ...remaining for further processing  : 127
% 0.20/0.39  # Other redundant clauses eliminated   : 0
% 0.20/0.39  # Clauses deleted for lack of memory   : 0
% 0.20/0.39  # Backward-subsumed                    : 26
% 0.20/0.39  # Backward-rewritten                   : 7
% 0.20/0.39  # Generated clauses                    : 106
% 0.20/0.39  # ...of the previous two non-trivial   : 108
% 0.20/0.39  # Contextual simplify-reflections      : 6
% 0.20/0.39  # Paramodulations                      : 106
% 0.20/0.39  # Factorizations                       : 0
% 0.20/0.39  # Equation resolutions                 : 0
% 0.20/0.39  # Propositional unsat checks           : 0
% 0.20/0.39  #    Propositional check models        : 0
% 0.20/0.39  #    Propositional check unsatisfiable : 0
% 0.20/0.39  #    Propositional clauses             : 0
% 0.20/0.39  #    Propositional clauses after purity: 0
% 0.20/0.39  #    Propositional unsat core size     : 0
% 0.20/0.39  #    Propositional preprocessing time  : 0.000
% 0.20/0.39  #    Propositional encoding time       : 0.000
% 0.20/0.39  #    Propositional solver time         : 0.000
% 0.20/0.39  #    Success case prop preproc time    : 0.000
% 0.20/0.39  #    Success case prop encoding time   : 0.000
% 0.20/0.39  #    Success case prop solver time     : 0.000
% 0.20/0.39  # Current number of processed clauses  : 69
% 0.20/0.39  #    Positive orientable unit clauses  : 24
% 0.20/0.39  #    Positive unorientable unit clauses: 0
% 0.20/0.39  #    Negative unit clauses             : 5
% 0.20/0.39  #    Non-unit-clauses                  : 40
% 0.20/0.39  # Current number of unprocessed clauses: 9
% 0.20/0.39  # ...number of literals in the above   : 117
% 0.20/0.39  # Current number of archived formulas  : 0
% 0.20/0.39  # Current number of archived clauses   : 58
% 0.20/0.39  # Clause-clause subsumption calls (NU) : 2595
% 0.20/0.39  # Rec. Clause-clause subsumption calls : 128
% 0.20/0.39  # Non-unit clause-clause subsumptions  : 42
% 0.20/0.39  # Unit Clause-clause subsumption calls : 142
% 0.20/0.39  # Rewrite failures with RHS unbound    : 0
% 0.20/0.39  # BW rewrite match attempts            : 53
% 0.20/0.39  # BW rewrite match successes           : 5
% 0.20/0.39  # Condensation attempts                : 0
% 0.20/0.39  # Condensation successes               : 0
% 0.20/0.39  # Termbank termtop insertions          : 12153
% 0.20/0.39  
% 0.20/0.39  # -------------------------------------------------
% 0.20/0.39  # User time                : 0.042 s
% 0.20/0.39  # System time              : 0.006 s
% 0.20/0.39  # Total time               : 0.048 s
% 0.20/0.39  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
