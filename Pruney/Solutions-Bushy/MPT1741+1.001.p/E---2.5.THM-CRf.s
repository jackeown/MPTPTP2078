%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1741+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:41 EST 2020

% Result     : Theorem 0.15s
% Output     : CNFRefutation 0.15s
% Verified   : 
% Statistics : Number of formulae       :   95 (5387 expanded)
%              Number of clauses        :   78 (1756 expanded)
%              Number of leaves         :    8 (1255 expanded)
%              Depth                    :   17
%              Number of atoms          :  557 (83650 expanded)
%              Number of equality atoms :   10 (3703 expanded)
%              Maximal formula depth    :   29 (   6 average)
%              Maximal clause size      :  111 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t50_tmap_1,conjecture,(
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
             => ( ( u1_struct_0(X2) = u1_struct_0(X3)
                  & r1_tarski(u1_pre_topc(X3),u1_pre_topc(X2)) )
               => ! [X4] :
                    ( ( v1_funct_1(X4)
                      & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                   => ! [X5] :
                        ( ( v1_funct_1(X5)
                          & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X3))
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) )
                       => ( r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X3),X4,X5)
                         => ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X1))
                             => ( r1_tmap_1(X1,X2,X4,X6)
                               => r1_tmap_1(X1,X3,X5,X6) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tmap_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tmap_1)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_funct_2)).

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
               => ( ( u1_struct_0(X2) = u1_struct_0(X3)
                    & r1_tarski(u1_pre_topc(X3),u1_pre_topc(X2)) )
                 => ! [X4] :
                      ( ( v1_funct_1(X4)
                        & v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X2))
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
                     => ! [X5] :
                          ( ( v1_funct_1(X5)
                            & v1_funct_2(X5,u1_struct_0(X1),u1_struct_0(X3))
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3)))) )
                         => ( r1_funct_2(u1_struct_0(X1),u1_struct_0(X2),u1_struct_0(X1),u1_struct_0(X3),X4,X5)
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X1))
                               => ( r1_tmap_1(X1,X2,X4,X6)
                                 => r1_tmap_1(X1,X3,X5,X6) ) ) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t50_tmap_1])).

fof(c_0_9,plain,(
    ! [X19,X20,X21,X22,X23,X26] :
      ( ( m1_subset_1(esk1_5(X19,X20,X21,X22,X23),k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v3_pre_topc(X23,X20)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X19),u1_struct_0(X20),X21,X22),X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r1_tmap_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( v3_pre_topc(esk1_5(X19,X20,X21,X22,X23),X19)
        | ~ v3_pre_topc(X23,X20)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X19),u1_struct_0(X20),X21,X22),X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r1_tmap_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(X22,esk1_5(X19,X20,X21,X22,X23))
        | ~ v3_pre_topc(X23,X20)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X19),u1_struct_0(X20),X21,X22),X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r1_tmap_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r1_tarski(k7_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,esk1_5(X19,X20,X21,X22,X23)),X23)
        | ~ v3_pre_topc(X23,X20)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X19),u1_struct_0(X20),X21,X22),X23)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X20)))
        | ~ r1_tmap_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( m1_subset_1(esk2_4(X19,X20,X21,X22),k1_zfmisc_1(u1_struct_0(X20)))
        | r1_tmap_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( v3_pre_topc(esk2_4(X19,X20,X21,X22),X20)
        | r1_tmap_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( r2_hidden(k3_funct_2(u1_struct_0(X19),u1_struct_0(X20),X21,X22),esk2_4(X19,X20,X21,X22))
        | r1_tmap_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) )
      & ( ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X19)))
        | ~ v3_pre_topc(X26,X19)
        | ~ r2_hidden(X22,X26)
        | ~ r1_tarski(k7_relset_1(u1_struct_0(X19),u1_struct_0(X20),X21,X26),esk2_4(X19,X20,X21,X22))
        | r1_tmap_1(X19,X20,X21,X22)
        | ~ m1_subset_1(X22,u1_struct_0(X19))
        | ~ v1_funct_1(X21)
        | ~ v1_funct_2(X21,u1_struct_0(X19),u1_struct_0(X20))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X19),u1_struct_0(X20))))
        | v2_struct_0(X20)
        | ~ v2_pre_topc(X20)
        | ~ l1_pre_topc(X20)
        | v2_struct_0(X19)
        | ~ v2_pre_topc(X19)
        | ~ l1_pre_topc(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tmap_1])])])])])])).

fof(c_0_10,negated_conjecture,
    ( ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & ~ v2_struct_0(esk4_0)
    & v2_pre_topc(esk4_0)
    & l1_pre_topc(esk4_0)
    & ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & u1_struct_0(esk4_0) = u1_struct_0(esk5_0)
    & r1_tarski(u1_pre_topc(esk5_0),u1_pre_topc(esk4_0))
    & v1_funct_1(esk6_0)
    & v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0))))
    & v1_funct_1(esk7_0)
    & v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk5_0))))
    & r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk5_0),esk6_0,esk7_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk3_0))
    & r1_tmap_1(esk3_0,esk4_0,esk6_0,esk8_0)
    & ~ r1_tmap_1(esk3_0,esk5_0,esk7_0,esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_8])])])])).

cnf(c_0_11,plain,
    ( v3_pre_topc(esk2_4(X1,X2,X3,X4),X2)
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
    ( u1_struct_0(esk4_0) = u1_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_13,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_14,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_16,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_17,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk5_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_18,negated_conjecture,
    ( r1_tmap_1(X1,esk5_0,X2,X3)
    | v2_struct_0(X1)
    | v3_pre_topc(esk2_4(X1,esk5_0,X2,X3),esk5_0)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_11,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_19,negated_conjecture,
    ( v1_funct_2(esk7_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[c_0_16,c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_21,negated_conjecture,
    ( v1_funct_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_22,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(rw,[status(thm)],[c_0_17,c_0_12])).

cnf(c_0_23,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_24,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk2_4(X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X2)))
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

fof(c_0_26,plain,(
    ! [X7,X8] :
      ( ( ~ v3_pre_topc(X8,X7)
        | r2_hidden(X8,u1_pre_topc(X7))
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) )
      & ( ~ r2_hidden(X8,u1_pre_topc(X7))
        | v3_pre_topc(X8,X7)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X7)))
        | ~ l1_pre_topc(X7) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_27,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk5_0,esk7_0,X1)
    | v3_pre_topc(esk2_4(esk3_0,esk5_0,esk7_0,X1),esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_18,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_29,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk5_0,esk7_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_30,negated_conjecture,
    ( r1_tmap_1(X1,esk5_0,X2,X3)
    | v2_struct_0(X1)
    | m1_subset_1(esk2_4(X1,esk5_0,X2,X3),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_31,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_32,negated_conjecture,
    ( v3_pre_topc(esk2_4(esk3_0,esk5_0,esk7_0,esk8_0),esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_28]),c_0_29])).

cnf(c_0_33,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk5_0,esk7_0,X1)
    | m1_subset_1(esk2_4(esk3_0,esk5_0,esk7_0,X1),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

fof(c_0_34,plain,(
    ! [X27,X28,X29] :
      ( ~ r2_hidden(X27,X28)
      | ~ m1_subset_1(X28,k1_zfmisc_1(X29))
      | m1_subset_1(X27,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(esk2_4(esk3_0,esk5_0,esk7_0,esk8_0),u1_pre_topc(esk5_0))
    | ~ m1_subset_1(esk2_4(esk3_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_12]),c_0_14])])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_4(esk3_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_28]),c_0_29])).

fof(c_0_37,plain,(
    ! [X17,X18] :
      ( ( ~ m1_subset_1(X17,k1_zfmisc_1(X18))
        | r1_tarski(X17,X18) )
      & ( ~ r1_tarski(X17,X18)
        | m1_subset_1(X17,k1_zfmisc_1(X18)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_38,plain,(
    ! [X30,X31,X32] :
      ( ~ r2_hidden(X30,X31)
      | ~ m1_subset_1(X31,k1_zfmisc_1(X32))
      | ~ v1_xboole_0(X32) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_39,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_40,negated_conjecture,
    ( r2_hidden(esk2_4(esk3_0,esk5_0,esk7_0,esk8_0),u1_pre_topc(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_35,c_0_36])])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk5_0),u1_pre_topc(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_43,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_44,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),esk2_4(X1,X2,X3,X4))
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

fof(c_0_45,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,X16)
      | v1_xboole_0(X16)
      | r2_hidden(X15,X16) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(esk2_4(esk3_0,esk5_0,esk7_0,esk8_0),X1)
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(u1_pre_topc(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_48,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(u1_pre_topc(esk5_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( r1_tmap_1(X1,esk5_0,X2,X3)
    | v2_struct_0(X1)
    | r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk4_0),X2,X3),esk2_4(X1,esk5_0,X2,X3))
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_50,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(esk2_4(esk3_0,esk5_0,esk7_0,esk8_0),u1_pre_topc(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(u1_pre_topc(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

fof(c_0_53,plain,(
    ! [X9,X10,X11,X12,X13,X14] :
      ( ( ~ r1_funct_2(X9,X10,X11,X12,X13,X14)
        | X13 = X14
        | v1_xboole_0(X10)
        | v1_xboole_0(X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X9,X10)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) )
      & ( X13 != X14
        | r1_funct_2(X9,X10,X11,X12,X13,X14)
        | v1_xboole_0(X10)
        | v1_xboole_0(X12)
        | ~ v1_funct_1(X13)
        | ~ v1_funct_2(X13,X9,X10)
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
        | ~ v1_funct_1(X14)
        | ~ v1_funct_2(X14,X11,X12)
        | ~ m1_subset_1(X14,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_54,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk5_0),esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_55,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk5_0,esk7_0,X1)
    | r2_hidden(k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk7_0,X1),esk2_4(esk3_0,esk5_0,esk7_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_19]),c_0_20]),c_0_21]),c_0_22]),c_0_23])]),c_0_24])).

cnf(c_0_56,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk2_4(esk3_0,esk5_0,esk7_0,esk8_0),u1_pre_topc(esk4_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_58,negated_conjecture,
    ( l1_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_59,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk6_0,esk7_0) ),
    inference(rw,[status(thm)],[c_0_54,c_0_12])).

cnf(c_0_61,negated_conjecture,
    ( v1_funct_2(esk6_0,u1_struct_0(esk3_0),u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_62,negated_conjecture,
    ( v1_funct_1(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk7_0,esk8_0),esk2_4(esk3_0,esk5_0,esk7_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_55,c_0_28]),c_0_29])).

cnf(c_0_65,negated_conjecture,
    ( v3_pre_topc(esk2_4(esk3_0,esk5_0,esk7_0,esk8_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_36]),c_0_58])])).

cnf(c_0_66,negated_conjecture,
    ( esk7_0 = esk6_0
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_19]),c_0_61]),c_0_21]),c_0_62]),c_0_22]),c_0_63])])).

cnf(c_0_67,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(esk2_4(esk3_0,esk5_0,esk7_0,esk8_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_43,c_0_64])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | v3_pre_topc(esk2_4(esk3_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_65,c_0_66])).

cnf(c_0_69,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_67,c_0_36])).

cnf(c_0_70,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(esk2_4(esk3_0,esk5_0,esk6_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_66])).

cnf(c_0_71,plain,
    ( r1_tmap_1(X2,X4,X5,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X4),X5,X1),esk2_4(X2,X4,X5,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_9])).

cnf(c_0_72,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk1_5(X1,X2,X3,X4,X5)),X5)
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
    ( v3_pre_topc(esk2_4(esk3_0,esk5_0,esk6_0,esk8_0),esk4_0) ),
    inference(sr,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( v2_pre_topc(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_75,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk2_4(esk3_0,esk5_0,esk6_0,esk8_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(sr,[status(thm)],[c_0_70,c_0_69])).

cnf(c_0_77,negated_conjecture,
    ( esk7_0 = esk6_0 ),
    inference(sr,[status(thm)],[c_0_66,c_0_69])).

cnf(c_0_78,plain,
    ( r2_hidden(X1,esk1_5(X2,X3,X4,X1,X5))
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

cnf(c_0_79,plain,
    ( v3_pre_topc(esk1_5(X1,X2,X3,X4,X5),X1)
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

cnf(c_0_80,plain,
    ( m1_subset_1(esk1_5(X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(X1)))
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

cnf(c_0_81,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X5),esk2_4(X1,X2,X3,X4))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(X4,X5)
    | ~ v3_pre_topc(X5,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_71,c_0_39])).

cnf(c_0_82,negated_conjecture,
    ( v2_struct_0(X1)
    | r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(esk4_0),X2,esk1_5(X1,esk4_0,X2,X3,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))
    | ~ r1_tmap_1(X1,esk4_0,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk4_0),X2,X3),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_74]),c_0_58])]),c_0_75]),c_0_76])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tmap_1(esk3_0,esk4_0,esk6_0,esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_10])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k3_funct_2(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk6_0,esk8_0),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_64,c_0_77]),c_0_77])).

cnf(c_0_85,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(X2,esk1_5(X1,esk4_0,X3,X2,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)))
    | ~ r1_tmap_1(X1,esk4_0,X3,X2)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X3)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk4_0),X3,X2),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_73]),c_0_74]),c_0_58])]),c_0_75]),c_0_76])])).

cnf(c_0_86,negated_conjecture,
    ( v2_struct_0(X1)
    | v3_pre_topc(esk1_5(X1,esk4_0,X2,X3,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),X1)
    | ~ r1_tmap_1(X1,esk4_0,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk4_0),X2,X3),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_73]),c_0_74]),c_0_58])]),c_0_75]),c_0_76])])).

cnf(c_0_87,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk1_5(X1,esk4_0,X2,X3,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_tmap_1(X1,esk4_0,X2,X3)
    | ~ v2_pre_topc(X1)
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk4_0),X2,X3),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_73]),c_0_74]),c_0_58])]),c_0_75]),c_0_76])])).

cnf(c_0_88,negated_conjecture,
    ( r1_tmap_1(X1,esk5_0,X2,X3)
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(esk4_0),X2,X4),esk2_4(X1,esk5_0,X2,X3))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk4_0))
    | ~ v1_funct_1(X2)
    | ~ r2_hidden(X3,X4)
    | ~ v3_pre_topc(X4,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk4_0))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_12]),c_0_13]),c_0_14])]),c_0_15])).

cnf(c_0_89,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk3_0),u1_struct_0(esk4_0),esk6_0,esk1_5(esk3_0,esk4_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))),esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_83]),c_0_20]),c_0_61]),c_0_62]),c_0_84]),c_0_63]),c_0_28]),c_0_23])]),c_0_24])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk8_0,esk1_5(esk3_0,esk4_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_83]),c_0_20]),c_0_61]),c_0_62]),c_0_84]),c_0_63]),c_0_28]),c_0_23])]),c_0_24])).

cnf(c_0_91,negated_conjecture,
    ( v3_pre_topc(esk1_5(esk3_0,esk4_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_83]),c_0_20]),c_0_61]),c_0_62]),c_0_84]),c_0_63]),c_0_28]),c_0_23])]),c_0_24])).

cnf(c_0_92,negated_conjecture,
    ( m1_subset_1(esk1_5(esk3_0,esk4_0,esk6_0,esk8_0,esk2_4(esk3_0,esk5_0,esk6_0,esk8_0)),k1_zfmisc_1(u1_struct_0(esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_83]),c_0_20]),c_0_61]),c_0_62]),c_0_84]),c_0_63]),c_0_28]),c_0_23])]),c_0_24])).

cnf(c_0_93,negated_conjecture,
    ( ~ r1_tmap_1(esk3_0,esk5_0,esk6_0,esk8_0) ),
    inference(rw,[status(thm)],[c_0_29,c_0_77])).

cnf(c_0_94,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_89]),c_0_20]),c_0_61]),c_0_62]),c_0_90]),c_0_91]),c_0_63]),c_0_92]),c_0_23])]),c_0_93]),c_0_24]),
    [proof]).

%------------------------------------------------------------------------------
