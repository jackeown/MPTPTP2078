%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t51_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:16 EDT 2019

% Result     : Theorem 1.01s
% Output     : CNFRefutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :   96 (4495 expanded)
%              Number of clauses        :   79 (1374 expanded)
%              Number of leaves         :    8 (1077 expanded)
%              Depth                    :   16
%              Number of atoms          :  556 (78678 expanded)
%              Number of equality atoms :   14 (6006 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :  111 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_tmap_1,conjecture,(
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
                & v2_pre_topc(X3)
                & l1_pre_topc(X3) )
             => ( ( u1_struct_0(X1) = u1_struct_0(X2)
                  & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                       => ( r1_funct_2(u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X1))
                             => ! [X7] :
                                  ( m1_subset_1(X7,u1_struct_0(X2))
                                 => ( ( X6 = X7
                                      & r1_tmap_1(X2,X3,X5,X7) )
                                   => r1_tmap_1(X1,X3,X4,X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t51_tmap_1.p',t51_tmap_1)).

fof(t48_tmap_1,axiom,(
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
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( r1_tmap_1(X1,X2,X3,X4)
                  <=> ! [X5] :
                        ( m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
                       => ~ ( v3_pre_topc(X5,X2)
                            & r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X5)
                            & ! [X6] :
                                ( m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X1)))
                               => ~ ( v3_pre_topc(X6,X1)
                                    & r2_hidden(X4,X6)
                                    & r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X6),X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t51_tmap_1.p',t48_tmap_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t51_tmap_1.p',t5_subset)).

fof(redefinition_r1_funct_2,axiom,(
    ! [X1,X2,X3,X4,X5,X6] :
      ( ( ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X4)
        & v1_funct_1(X5)
        & v1_funct_2(X5,X1,X2)
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X6)
        & v1_funct_2(X6,X3,X4)
        & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
     => ( r1_funct_2(X1,X2,X3,X4,X5,X6)
      <=> X5 = X6 ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t51_tmap_1.p',redefinition_r1_funct_2)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t51_tmap_1.p',d5_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t51_tmap_1.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t51_tmap_1.p',t3_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t51_tmap_1.p',t2_subset)).

fof(c_0_8,negated_conjecture,(
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
                  & v2_pre_topc(X3)
                  & l1_pre_topc(X3) )
               => ( ( u1_struct_0(X1) = u1_struct_0(X2)
                    & r1_tarski(u1_pre_topc(X2),u1_pre_topc(X1)) )
                 => ! [X4] :
                      ( ( v1_funct_1(X4)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) )
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3)))) )
                         => ( r1_funct_2(u1_struct_0(X1),u1_struct_0(X3),u1_struct_0(X2),u1_struct_0(X3),X4,X5)
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X1))
                               => ! [X7] :
                                    ( m1_subset_1(X7,u1_struct_0(X2))
                                   => ( ( X6 = X7
                                        & r1_tmap_1(X2,X3,X5,X7) )
                                     => r1_tmap_1(X1,X3,X4,X6) ) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_tmap_1])).

fof(c_0_9,plain,(
    ! [X65,X66,X67,X68,X69,X72] :
      ( ( m1_subset_1(esk11_5(X65,X66,X67,X68,X69),k1_zfmisc_1(u1_struct_0(X65)))
        | ~ v3_pre_topc(X69,X66)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X65),u1_struct_0(X66),X67,X68),X69)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X66)))
        | ~ r1_tmap_1(X65,X66,X67,X68)
        | ~ m1_subset_1(X68,u1_struct_0(X65))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(X66))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | v2_struct_0(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66)
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) )
      & ( v3_pre_topc(esk11_5(X65,X66,X67,X68,X69),X65)
        | ~ v3_pre_topc(X69,X66)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X65),u1_struct_0(X66),X67,X68),X69)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X66)))
        | ~ r1_tmap_1(X65,X66,X67,X68)
        | ~ m1_subset_1(X68,u1_struct_0(X65))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(X66))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | v2_struct_0(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66)
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) )
      & ( r2_hidden(X68,esk11_5(X65,X66,X67,X68,X69))
        | ~ v3_pre_topc(X69,X66)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X65),u1_struct_0(X66),X67,X68),X69)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X66)))
        | ~ r1_tmap_1(X65,X66,X67,X68)
        | ~ m1_subset_1(X68,u1_struct_0(X65))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(X66))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | v2_struct_0(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66)
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) )
      & ( r1_tarski(k7_relset_1(u1_struct_0(X65),u1_struct_0(X66),X67,esk11_5(X65,X66,X67,X68,X69)),X69)
        | ~ v3_pre_topc(X69,X66)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X65),u1_struct_0(X66),X67,X68),X69)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X66)))
        | ~ r1_tmap_1(X65,X66,X67,X68)
        | ~ m1_subset_1(X68,u1_struct_0(X65))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(X66))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | v2_struct_0(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66)
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) )
      & ( m1_subset_1(esk12_4(X65,X66,X67,X68),k1_zfmisc_1(u1_struct_0(X66)))
        | r1_tmap_1(X65,X66,X67,X68)
        | ~ m1_subset_1(X68,u1_struct_0(X65))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(X66))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | v2_struct_0(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66)
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) )
      & ( v3_pre_topc(esk12_4(X65,X66,X67,X68),X66)
        | r1_tmap_1(X65,X66,X67,X68)
        | ~ m1_subset_1(X68,u1_struct_0(X65))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(X66))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | v2_struct_0(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66)
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) )
      & ( r2_hidden(k3_funct_2(u1_struct_0(X65),u1_struct_0(X66),X67,X68),esk12_4(X65,X66,X67,X68))
        | r1_tmap_1(X65,X66,X67,X68)
        | ~ m1_subset_1(X68,u1_struct_0(X65))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(X66))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | v2_struct_0(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66)
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) )
      & ( ~ m1_subset_1(X72,k1_zfmisc_1(u1_struct_0(X65)))
        | ~ v3_pre_topc(X72,X65)
        | ~ r2_hidden(X68,X72)
        | ~ r1_tarski(k7_relset_1(u1_struct_0(X65),u1_struct_0(X66),X67,X72),esk12_4(X65,X66,X67,X68))
        | r1_tmap_1(X65,X66,X67,X68)
        | ~ m1_subset_1(X68,u1_struct_0(X65))
        | ~ v1_funct_1(X67)
        | ~ v1_funct_2(X67,u1_struct_0(X65),u1_struct_0(X66))
        | ~ m1_subset_1(X67,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X65),u1_struct_0(X66))))
        | v2_struct_0(X66)
        | ~ v2_pre_topc(X66)
        | ~ l1_pre_topc(X66)
        | v2_struct_0(X65)
        | ~ v2_pre_topc(X65)
        | ~ l1_pre_topc(X65) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tmap_1])])])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & u1_struct_0(esk1_0) = u1_struct_0(esk2_0)
    & r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0))))
    & r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk2_0))
    & esk6_0 = esk7_0
    & r1_tmap_1(esk2_0,esk3_0,esk5_0,esk7_0)
    & ~ r1_tmap_1(esk1_0,esk3_0,esk4_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),esk12_4(X1,X2,X3,X4))
    | r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_12,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_20,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk2_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( u1_struct_0(esk1_0) = u1_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_23,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_24,plain,(
    ! [X76,X77,X78] :
      ( ~ r2_hidden(X76,X77)
      | ~ m1_subset_1(X77,k1_zfmisc_1(X78))
      | ~ v1_xboole_0(X78) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_25,negated_conjecture,
    ( r2_hidden(k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),esk4_0,X1),esk12_4(esk1_0,esk3_0,esk4_0,X1))
    | r1_tmap_1(esk1_0,esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_27,negated_conjecture,
    ( ~ r1_tmap_1(esk1_0,esk3_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_28,plain,
    ( m1_subset_1(esk12_4(X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X2)))
    | r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_29,plain,
    ( v3_pre_topc(esk12_4(X1,X2,X3,X4),X2)
    | r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_30,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk3_0)) ),
    inference(rw,[status(thm)],[c_0_21,c_0_22])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0)))) ),
    inference(rw,[status(thm)],[c_0_23,c_0_22])).

cnf(c_0_32,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

fof(c_0_33,plain,(
    ! [X41,X42,X43,X44,X45,X46] :
      ( ( ~ r1_funct_2(X41,X42,X43,X44,X45,X46)
        | X45 = X46
        | v1_xboole_0(X42)
        | v1_xboole_0(X44)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X41,X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X43,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) )
      & ( X45 != X46
        | r1_funct_2(X41,X42,X43,X44,X45,X46)
        | v1_xboole_0(X42)
        | v1_xboole_0(X44)
        | ~ v1_funct_1(X45)
        | ~ v1_funct_2(X45,X41,X42)
        | ~ m1_subset_1(X45,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
        | ~ v1_funct_1(X46)
        | ~ v1_funct_2(X46,X43,X44)
        | ~ m1_subset_1(X46,k1_zfmisc_1(k2_zfmisc_1(X43,X44))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_34,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk3_0),esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_35,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,negated_conjecture,
    ( r2_hidden(k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),esk4_0,esk6_0),esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_26]),c_0_27])).

cnf(c_0_37,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk3_0,esk4_0,X1)
    | m1_subset_1(esk12_4(esk1_0,esk3_0,esk4_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_38,negated_conjecture,
    ( v3_pre_topc(esk12_4(esk1_0,esk3_0,esk5_0,X1),esk3_0)
    | r1_tmap_1(esk1_0,esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk3_0,esk5_0,X1)
    | m1_subset_1(esk12_4(esk1_0,esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk3_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_30]),c_0_31]),c_0_32]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

cnf(c_0_40,plain,
    ( X5 = X6
    | v1_xboole_0(X2)
    | v1_xboole_0(X4)
    | ~ r1_funct_2(X1,X2,X3,X4,X5,X6)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,X1,X2)
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X6)
    | ~ v1_funct_2(X6,X3,X4)
    | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_41,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk3_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_34,c_0_22])).

cnf(c_0_42,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(esk12_4(esk1_0,esk3_0,esk4_0,esk6_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk12_4(esk1_0,esk3_0,esk4_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_26]),c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk3_0,esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_45,negated_conjecture,
    ( esk6_0 = esk7_0 ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_46,plain,
    ( v3_pre_topc(esk11_5(X1,X2,X3,X4,X5),X1)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X5,X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_47,negated_conjecture,
    ( v3_pre_topc(esk12_4(esk1_0,esk3_0,esk5_0,esk6_0),esk3_0)
    | r1_tmap_1(esk1_0,esk3_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_38,c_0_26])).

cnf(c_0_48,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk3_0,esk5_0,esk6_0)
    | m1_subset_1(esk12_4(esk1_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(spm,[status(thm)],[c_0_39,c_0_26])).

cnf(c_0_49,negated_conjecture,
    ( esk5_0 = esk4_0
    | v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_31]),c_0_13]),c_0_30]),c_0_12]),c_0_32]),c_0_14])])).

cnf(c_0_50,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk3_0,esk5_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( v3_pre_topc(esk11_5(X1,esk3_0,X2,X3,esk12_4(esk1_0,esk3_0,esk5_0,esk6_0)),X1)
    | r1_tmap_1(esk1_0,esk3_0,esk5_0,esk6_0)
    | v2_struct_0(X1)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk3_0),X2,X3),esk12_4(esk1_0,esk3_0,esk5_0,esk6_0))
    | ~ r1_tmap_1(X1,esk3_0,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_15]),c_0_17])]),c_0_19]),c_0_48])).

cnf(c_0_53,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(sr,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk3_0))
    | r1_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_49])).

cnf(c_0_55,negated_conjecture,
    ( v3_pre_topc(esk12_4(esk1_0,esk3_0,esk4_0,X1),esk3_0)
    | r1_tmap_1(esk1_0,esk3_0,esk4_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_12]),c_0_13]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_19]),c_0_20])).

fof(c_0_56,plain,(
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

cnf(c_0_57,negated_conjecture,
    ( v3_pre_topc(esk11_5(X1,esk3_0,X2,X3,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk3_0),X2,X3),esk12_4(esk1_0,esk3_0,esk4_0,esk6_0))
    | ~ r1_tmap_1(X1,esk3_0,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_52,c_0_53]),c_0_53]),c_0_53]),c_0_27])).

cnf(c_0_58,negated_conjecture,
    ( r1_tmap_1(esk2_0,esk3_0,esk4_0,esk6_0) ),
    inference(sr,[status(thm)],[c_0_54,c_0_50])).

cnf(c_0_59,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_60,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_61,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_62,plain,
    ( m1_subset_1(esk11_5(X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X5,X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_63,negated_conjecture,
    ( v3_pre_topc(esk12_4(esk1_0,esk3_0,esk4_0,esk6_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_26]),c_0_27])).

cnf(c_0_64,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( v3_pre_topc(esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_22]),c_0_36]),c_0_22]),c_0_13]),c_0_22]),c_0_26]),c_0_22]),c_0_12]),c_0_14]),c_0_59]),c_0_60])]),c_0_61])).

cnf(c_0_66,negated_conjecture,
    ( m1_subset_1(esk11_5(X1,esk3_0,X2,X3,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk3_0),X2,X3),esk12_4(esk1_0,esk3_0,esk4_0,esk6_0))
    | ~ r1_tmap_1(X1,esk3_0,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_43]),c_0_15]),c_0_17])]),c_0_19])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,esk11_5(X2,X3,X4,X1,X5))
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X5,X3)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X2),u1_struct_0(X3),X4,X1),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ r1_tmap_1(X2,X3,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v2_pre_topc(X3)
    | ~ l1_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

fof(c_0_68,plain,(
    ! [X73,X74,X75] :
      ( ~ r2_hidden(X73,X74)
      | ~ m1_subset_1(X74,k1_zfmisc_1(X75))
      | m1_subset_1(X73,X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),u1_pre_topc(esk2_0))
    | ~ m1_subset_1(esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_22]),c_0_59])])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_58]),c_0_22]),c_0_22]),c_0_36]),c_0_22]),c_0_13]),c_0_22]),c_0_26]),c_0_22]),c_0_12]),c_0_14]),c_0_59]),c_0_60])]),c_0_61])).

fof(c_0_71,plain,(
    ! [X63,X64] :
      ( ( ~ m1_subset_1(X63,k1_zfmisc_1(X64))
        | r1_tarski(X63,X64) )
      & ( ~ r1_tarski(X63,X64)
        | m1_subset_1(X63,k1_zfmisc_1(X64)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_72,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk11_5(X1,X2,X3,X4,X5)),X5)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X5,X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),X5)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ r1_tmap_1(X1,X2,X3,X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(X1,esk11_5(X2,esk3_0,X3,X1,esk12_4(esk1_0,esk3_0,esk5_0,esk6_0)))
    | r1_tmap_1(esk1_0,esk3_0,esk5_0,esk6_0)
    | v2_struct_0(X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X2),u1_struct_0(esk3_0),X3,X1),esk12_4(esk1_0,esk3_0,esk5_0,esk6_0))
    | ~ r1_tmap_1(X2,esk3_0,X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_47]),c_0_15]),c_0_17])]),c_0_19]),c_0_48])).

cnf(c_0_74,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_68])).

cnf(c_0_75,negated_conjecture,
    ( r2_hidden(esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),u1_pre_topc(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_76,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk2_0),u1_pre_topc(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_78,plain,
    ( r1_tmap_1(X2,X4,X5,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X4),X5,X1),esk12_4(X2,X4,X5,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(esk3_0),X2,esk11_5(X1,esk3_0,X2,X3,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0))),esk12_4(esk1_0,esk3_0,esk4_0,esk6_0))
    | v2_struct_0(X1)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk3_0),X2,X3),esk12_4(esk1_0,esk3_0,esk4_0,esk6_0))
    | ~ r1_tmap_1(X1,esk3_0,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_63]),c_0_43]),c_0_15]),c_0_17])]),c_0_19])).

cnf(c_0_80,negated_conjecture,
    ( r2_hidden(X1,esk11_5(X2,esk3_0,X3,X1,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)))
    | v2_struct_0(X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X2),u1_struct_0(esk3_0),X3,X1),esk12_4(esk1_0,esk3_0,esk4_0,esk6_0))
    | ~ r1_tmap_1(X2,esk3_0,X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk3_0))))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk3_0))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_53]),c_0_53]),c_0_53]),c_0_27])).

fof(c_0_81,plain,(
    ! [X61,X62] :
      ( ~ m1_subset_1(X61,X62)
      | v1_xboole_0(X62)
      | r2_hidden(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_82,negated_conjecture,
    ( m1_subset_1(esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),X1)
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(u1_pre_topc(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_76,c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(u1_pre_topc(esk2_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_75])).

cnf(c_0_85,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X5,X1)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X5),esk12_4(X1,X2,X3,X4))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_78,c_0_74])).

cnf(c_0_86,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0),esk4_0,esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0))),esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_58]),c_0_22]),c_0_22]),c_0_36]),c_0_22]),c_0_13]),c_0_22]),c_0_26]),c_0_22]),c_0_12]),c_0_14]),c_0_59]),c_0_60])]),c_0_61])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk6_0,esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_58]),c_0_22]),c_0_36]),c_0_22]),c_0_13]),c_0_22]),c_0_26]),c_0_22]),c_0_12]),c_0_14]),c_0_59]),c_0_60])]),c_0_61])).

cnf(c_0_88,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_81])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_90,negated_conjecture,
    ( ~ v1_xboole_0(u1_pre_topc(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_84,c_0_83])).

cnf(c_0_91,negated_conjecture,
    ( ~ v3_pre_topc(esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),esk1_0)
    | ~ m1_subset_1(esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_87]),c_0_13]),c_0_12]),c_0_14]),c_0_15]),c_0_16]),c_0_17]),c_0_18])]),c_0_27]),c_0_19]),c_0_20])).

cnf(c_0_92,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),u1_pre_topc(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_90])).

cnf(c_0_94,negated_conjecture,
    ( ~ v3_pre_topc(esk11_5(esk2_0,esk3_0,esk4_0,esk6_0,esk12_4(esk1_0,esk3_0,esk4_0,esk6_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_91,c_0_70])])).

cnf(c_0_95,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_70]),c_0_16])]),c_0_94]),
    [proof]).
%------------------------------------------------------------------------------
