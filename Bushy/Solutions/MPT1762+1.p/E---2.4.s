%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t73_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:20 EDT 2019

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 532 expanded)
%              Number of clauses        :   56 ( 189 expanded)
%              Number of leaves         :   11 ( 130 expanded)
%              Depth                    :   15
%              Number of atoms          :  395 (6263 expanded)
%              Number of equality atoms :   33 ( 323 expanded)
%              Maximal formula depth    :   23 (   6 average)
%              Maximal clause size      :   36 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',existence_m1_subset_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',t5_subset)).

fof(t73_tmap_1,conjecture,(
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
                        & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                     => ( m1_pre_topc(X3,X4)
                       => ! [X6] :
                            ( ( v1_funct_1(X6)
                              & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                           => ( ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X4))
                                 => ( r2_hidden(X7,u1_struct_0(X3))
                                   => k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7) = k1_funct_1(X6,X7) ) )
                             => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',t73_tmap_1)).

fof(t173_funct_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,X1,X2)
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
             => ! [X4] :
                  ( ( ~ v1_xboole_0(X4)
                    & m1_subset_1(X4,k1_zfmisc_1(X1)) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,X4,X2)
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,X1)
                           => ( r2_hidden(X6,X4)
                             => k3_funct_2(X1,X2,X3,X6) = k1_funct_1(X5,X6) ) )
                       => k2_partfun1(X1,X2,X3,X4) = X5 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',t173_funct_2)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',dt_m1_pre_topc)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',t1_tsep_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',d5_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',redefinition_r2_funct_2)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t73_tmap_1.p',dt_l1_pre_topc)).

fof(c_0_11,plain,(
    ! [X76,X77] :
      ( ~ m1_subset_1(X76,X77)
      | v1_xboole_0(X77)
      | r2_hidden(X76,X77) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_12,plain,(
    ! [X44] : m1_subset_1(esk10_1(X44),X44) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

fof(c_0_13,plain,(
    ! [X83,X84,X85] :
      ( ~ r2_hidden(X83,X84)
      | ~ m1_subset_1(X84,k1_zfmisc_1(X85))
      | ~ v1_xboole_0(X85) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_14,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_15,plain,
    ( m1_subset_1(esk10_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_16,negated_conjecture,(
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
                          & v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2)))) )
                       => ( m1_pre_topc(X3,X4)
                         => ! [X6] :
                              ( ( v1_funct_1(X6)
                                & v1_funct_2(X6,u1_struct_0(X3),u1_struct_0(X2))
                                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2)))) )
                             => ( ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X4))
                                   => ( r2_hidden(X7,u1_struct_0(X3))
                                     => k3_funct_2(u1_struct_0(X4),u1_struct_0(X2),X5,X7) = k1_funct_1(X6,X7) ) )
                               => r2_funct_2(u1_struct_0(X3),u1_struct_0(X2),k3_tmap_1(X1,X2,X4,X3,X5),X6) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t73_tmap_1])).

fof(c_0_17,plain,(
    ! [X66,X67,X68,X69,X70] :
      ( ( m1_subset_1(esk11_5(X66,X67,X68,X69,X70),X66)
        | k2_partfun1(X66,X67,X68,X69) = X70
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X69,X67)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X69,X67)))
        | v1_xboole_0(X69)
        | ~ m1_subset_1(X69,k1_zfmisc_1(X66))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
        | v1_xboole_0(X67)
        | v1_xboole_0(X66) )
      & ( r2_hidden(esk11_5(X66,X67,X68,X69,X70),X69)
        | k2_partfun1(X66,X67,X68,X69) = X70
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X69,X67)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X69,X67)))
        | v1_xboole_0(X69)
        | ~ m1_subset_1(X69,k1_zfmisc_1(X66))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
        | v1_xboole_0(X67)
        | v1_xboole_0(X66) )
      & ( k3_funct_2(X66,X67,X68,esk11_5(X66,X67,X68,X69,X70)) != k1_funct_1(X70,esk11_5(X66,X67,X68,X69,X70))
        | k2_partfun1(X66,X67,X68,X69) = X70
        | ~ v1_funct_1(X70)
        | ~ v1_funct_2(X70,X69,X67)
        | ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(X69,X67)))
        | v1_xboole_0(X69)
        | ~ m1_subset_1(X69,k1_zfmisc_1(X66))
        | ~ v1_funct_1(X68)
        | ~ v1_funct_2(X68,X66,X67)
        | ~ m1_subset_1(X68,k1_zfmisc_1(k2_zfmisc_1(X66,X67)))
        | v1_xboole_0(X67)
        | v1_xboole_0(X66) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t173_funct_2])])])])])])).

cnf(c_0_18,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk10_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_14,c_0_15])).

fof(c_0_20,plain,(
    ! [X38,X39] :
      ( ~ l1_pre_topc(X38)
      | ~ m1_pre_topc(X39,X38)
      | l1_pre_topc(X39) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_21,negated_conjecture,(
    ! [X14] :
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
      & v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0))))
      & m1_pre_topc(esk3_0,esk4_0)
      & v1_funct_1(esk6_0)
      & v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0))
      & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0))))
      & ( ~ m1_subset_1(X14,u1_struct_0(esk4_0))
        | ~ r2_hidden(X14,u1_struct_0(esk3_0))
        | k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,X14) = k1_funct_1(esk6_0,X14) )
      & ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk6_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])).

cnf(c_0_22,plain,
    ( r2_hidden(esk11_5(X1,X2,X3,X4,X5),X4)
    | k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_18,c_0_19])).

fof(c_0_24,plain,(
    ! [X74,X75] :
      ( ~ l1_pre_topc(X74)
      | ~ m1_pre_topc(X75,X74)
      | m1_subset_1(u1_struct_0(X75),k1_zfmisc_1(u1_struct_0(X74))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_25,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_pre_topc(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk11_5(X1,X2,X3,X4,X5),X1)
    | k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_29,plain,
    ( k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | r2_hidden(esk11_5(X1,X2,X3,X4,X5),X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_2(X5,X4,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_34,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])])).

cnf(c_0_36,plain,
    ( k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | m1_subset_1(esk11_5(X1,X2,X3,X4,X5),X1)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_2(X5,X4,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X3) ),
    inference(csr,[status(thm)],[c_0_28,c_0_23])).

cnf(c_0_37,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk3_0)) = esk6_0
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | r2_hidden(esk11_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])])).

cnf(c_0_38,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk4_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_40,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])])).

cnf(c_0_41,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_42,negated_conjecture,
    ( k2_partfun1(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk3_0)) = esk6_0
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | m1_subset_1(esk11_5(X1,u1_struct_0(esk2_0),X2,u1_struct_0(esk3_0),esk6_0),X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(esk2_0))))
    | ~ m1_subset_1(u1_struct_0(esk3_0),k1_zfmisc_1(X1))
    | ~ v1_funct_2(X2,X1,u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_36,c_0_30]),c_0_31]),c_0_32])])).

fof(c_0_43,plain,(
    ! [X17,X18,X19,X20,X21] :
      ( v2_struct_0(X17)
      | ~ v2_pre_topc(X17)
      | ~ l1_pre_topc(X17)
      | v2_struct_0(X18)
      | ~ v2_pre_topc(X18)
      | ~ l1_pre_topc(X18)
      | ~ m1_pre_topc(X19,X17)
      | ~ m1_pre_topc(X20,X17)
      | ~ v1_funct_1(X21)
      | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X18))
      | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X18))))
      | ~ m1_pre_topc(X20,X19)
      | k3_tmap_1(X17,X18,X19,X20,X21) = k2_partfun1(u1_struct_0(X19),u1_struct_0(X18),X21,u1_struct_0(X20)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d5_tmap_1])])])])).

fof(c_0_44,plain,(
    ! [X54,X55,X56,X57] :
      ( ( ~ r2_funct_2(X54,X55,X56,X57)
        | X56 = X57
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X54,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) )
      & ( X56 != X57
        | r2_funct_2(X54,X55,X56,X57)
        | ~ v1_funct_1(X56)
        | ~ v1_funct_2(X56,X54,X55)
        | ~ m1_subset_1(X56,k1_zfmisc_1(k2_zfmisc_1(X54,X55)))
        | ~ v1_funct_1(X57)
        | ~ v1_funct_2(X57,X54,X55)
        | ~ m1_subset_1(X57,k1_zfmisc_1(k2_zfmisc_1(X54,X55))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_r2_funct_2])])])).

cnf(c_0_45,negated_conjecture,
    ( k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,X1) = k1_funct_1(esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_46,negated_conjecture,
    ( esk6_0 = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk11_5(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_47,negated_conjecture,
    ( esk6_0 = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(esk11_5(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0),esk6_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_38]),c_0_39]),c_0_40]),c_0_41])])).

cnf(c_0_48,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,plain,
    ( r2_funct_2(X3,X4,X1,X2)
    | X1 != X2
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_50,plain,
    ( k2_partfun1(X1,X2,X3,X4) = X5
    | v1_xboole_0(X4)
    | v1_xboole_0(X2)
    | v1_xboole_0(X1)
    | k3_funct_2(X1,X2,X3,esk11_5(X1,X2,X3,X4,X5)) != k1_funct_1(X5,esk11_5(X1,X2,X3,X4,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X4,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_51,negated_conjecture,
    ( k1_funct_1(esk6_0,esk11_5(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0),esk6_0)) = k3_funct_2(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,esk11_5(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0),esk6_0))
    | esk6_0 = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_40])).

cnf(c_0_53,negated_conjecture,
    ( k3_tmap_1(X1,X2,esk4_0,esk3_0,X3) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(X2),X3,u1_struct_0(esk3_0))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X2))))
    | ~ v1_funct_2(X3,u1_struct_0(esk4_0),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(esk3_0,X1)
    | ~ m1_pre_topc(esk4_0,X1)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_48,c_0_34])).

cnf(c_0_54,negated_conjecture,
    ( m1_pre_topc(esk3_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_55,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_57,plain,
    ( r2_funct_2(X1,X2,X3,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X3,X1,X2)
    | ~ v1_funct_1(X3) ),
    inference(er,[status(thm)],[c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_59,negated_conjecture,
    ( esk6_0 = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_31]),c_0_39]),c_0_40]),c_0_30]),c_0_38]),c_0_32]),c_0_41])]),c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( k3_tmap_1(esk1_0,X1,esk4_0,esk3_0,X2) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(X1),X2,u1_struct_0(esk3_0))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk4_0),u1_struct_0(X1))))
    | ~ v1_funct_2(X2,u1_struct_0(esk4_0),u1_struct_0(X1))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_26]),c_0_27]),c_0_55])]),c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_63,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_64,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),esk6_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_30]),c_0_31]),c_0_32])])).

fof(c_0_65,plain,(
    ! [X93] :
      ( v2_struct_0(X93)
      | ~ l1_struct_0(X93)
      | ~ v1_xboole_0(u1_struct_0(X93)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | ~ r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0),k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( k3_tmap_1(esk1_0,esk2_0,esk4_0,esk3_0,esk5_0) = k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_38]),c_0_39]),c_0_41]),c_0_61]),c_0_62])]),c_0_63])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | v1_xboole_0(u1_struct_0(esk2_0))
    | r2_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk2_0),k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0)),k2_partfun1(u1_struct_0(esk4_0),u1_struct_0(esk2_0),esk5_0,u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_64,c_0_59])).

cnf(c_0_69,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(csr,[status(thm)],[inference(rw,[status(thm)],[c_0_66,c_0_67]),c_0_68])).

cnf(c_0_71,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_72,plain,(
    ! [X37] :
      ( ~ l1_pre_topc(X37)
      | l1_struct_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_73,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | ~ l1_struct_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71])).

cnf(c_0_74,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_72])).

cnf(c_0_75,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_54]),c_0_27])])).

cnf(c_0_76,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_74]),c_0_75])])).

cnf(c_0_77,negated_conjecture,
    ( ~ l1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_76]),c_0_63])).

cnf(c_0_78,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_74]),c_0_61])]),
    [proof]).
%------------------------------------------------------------------------------
