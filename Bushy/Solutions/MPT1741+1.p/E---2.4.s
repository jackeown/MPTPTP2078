%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t50_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:16 EDT 2019

% Result     : Theorem 8.08s
% Output     : CNFRefutation 8.08s
% Verified   : 
% Statistics : Number of formulae       :  107 (5539 expanded)
%              Number of clauses        :   86 (1824 expanded)
%              Number of leaves         :   10 (1295 expanded)
%              Depth                    :   17
%              Number of atoms          :  578 (84206 expanded)
%              Number of equality atoms :   10 (3715 expanded)
%              Maximal formula depth    :   29 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t50_tmap_1.p',t50_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t50_tmap_1.p',t48_tmap_1)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t50_tmap_1.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t50_tmap_1.p',existence_m1_subset_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t50_tmap_1.p',t4_subset)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t50_tmap_1.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t50_tmap_1.p',t5_subset)).

fof(d5_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v3_pre_topc(X2,X1)
          <=> r2_hidden(X2,u1_pre_topc(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t50_tmap_1.p',d5_pre_topc)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t50_tmap_1.p',t7_boole)).

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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t50_tmap_1.p',redefinition_r1_funct_2)).

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

fof(c_0_11,plain,(
    ! [X63,X64,X65,X66,X67,X70] :
      ( ( m1_subset_1(esk10_5(X63,X64,X65,X66,X67),k1_zfmisc_1(u1_struct_0(X63)))
        | ~ v3_pre_topc(X67,X64)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X63),u1_struct_0(X64),X65,X66),X67)
        | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X64)))
        | ~ r1_tmap_1(X63,X64,X65,X66)
        | ~ m1_subset_1(X66,u1_struct_0(X63))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,u1_struct_0(X63),u1_struct_0(X64))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X63),u1_struct_0(X64))))
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) )
      & ( v3_pre_topc(esk10_5(X63,X64,X65,X66,X67),X63)
        | ~ v3_pre_topc(X67,X64)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X63),u1_struct_0(X64),X65,X66),X67)
        | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X64)))
        | ~ r1_tmap_1(X63,X64,X65,X66)
        | ~ m1_subset_1(X66,u1_struct_0(X63))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,u1_struct_0(X63),u1_struct_0(X64))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X63),u1_struct_0(X64))))
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) )
      & ( r2_hidden(X66,esk10_5(X63,X64,X65,X66,X67))
        | ~ v3_pre_topc(X67,X64)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X63),u1_struct_0(X64),X65,X66),X67)
        | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X64)))
        | ~ r1_tmap_1(X63,X64,X65,X66)
        | ~ m1_subset_1(X66,u1_struct_0(X63))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,u1_struct_0(X63),u1_struct_0(X64))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X63),u1_struct_0(X64))))
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) )
      & ( r1_tarski(k7_relset_1(u1_struct_0(X63),u1_struct_0(X64),X65,esk10_5(X63,X64,X65,X66,X67)),X67)
        | ~ v3_pre_topc(X67,X64)
        | ~ r2_hidden(k3_funct_2(u1_struct_0(X63),u1_struct_0(X64),X65,X66),X67)
        | ~ m1_subset_1(X67,k1_zfmisc_1(u1_struct_0(X64)))
        | ~ r1_tmap_1(X63,X64,X65,X66)
        | ~ m1_subset_1(X66,u1_struct_0(X63))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,u1_struct_0(X63),u1_struct_0(X64))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X63),u1_struct_0(X64))))
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) )
      & ( m1_subset_1(esk11_4(X63,X64,X65,X66),k1_zfmisc_1(u1_struct_0(X64)))
        | r1_tmap_1(X63,X64,X65,X66)
        | ~ m1_subset_1(X66,u1_struct_0(X63))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,u1_struct_0(X63),u1_struct_0(X64))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X63),u1_struct_0(X64))))
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) )
      & ( v3_pre_topc(esk11_4(X63,X64,X65,X66),X64)
        | r1_tmap_1(X63,X64,X65,X66)
        | ~ m1_subset_1(X66,u1_struct_0(X63))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,u1_struct_0(X63),u1_struct_0(X64))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X63),u1_struct_0(X64))))
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) )
      & ( r2_hidden(k3_funct_2(u1_struct_0(X63),u1_struct_0(X64),X65,X66),esk11_4(X63,X64,X65,X66))
        | r1_tmap_1(X63,X64,X65,X66)
        | ~ m1_subset_1(X66,u1_struct_0(X63))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,u1_struct_0(X63),u1_struct_0(X64))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X63),u1_struct_0(X64))))
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) )
      & ( ~ m1_subset_1(X70,k1_zfmisc_1(u1_struct_0(X63)))
        | ~ v3_pre_topc(X70,X63)
        | ~ r2_hidden(X66,X70)
        | ~ r1_tarski(k7_relset_1(u1_struct_0(X63),u1_struct_0(X64),X65,X70),esk11_4(X63,X64,X65,X66))
        | r1_tmap_1(X63,X64,X65,X66)
        | ~ m1_subset_1(X66,u1_struct_0(X63))
        | ~ v1_funct_1(X65)
        | ~ v1_funct_2(X65,u1_struct_0(X63),u1_struct_0(X64))
        | ~ m1_subset_1(X65,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X63),u1_struct_0(X64))))
        | v2_struct_0(X64)
        | ~ v2_pre_topc(X64)
        | ~ l1_pre_topc(X64)
        | v2_struct_0(X63)
        | ~ v2_pre_topc(X63)
        | ~ l1_pre_topc(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t48_tmap_1])])])])])])).

fof(c_0_12,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v2_pre_topc(esk1_0)
    & l1_pre_topc(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v2_pre_topc(esk2_0)
    & l1_pre_topc(esk2_0)
    & ~ v2_struct_0(esk3_0)
    & v2_pre_topc(esk3_0)
    & l1_pre_topc(esk3_0)
    & u1_struct_0(esk2_0) = u1_struct_0(esk3_0)
    & r1_tarski(u1_pre_topc(esk3_0),u1_pre_topc(esk2_0))
    & v1_funct_1(esk4_0)
    & v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v1_funct_1(esk5_0)
    & v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk3_0))
    & m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0))))
    & r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),esk4_0,esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk1_0))
    & r1_tmap_1(esk1_0,esk2_0,esk4_0,esk6_0)
    & ~ r1_tmap_1(esk1_0,esk3_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_10])])])])).

fof(c_0_13,plain,(
    ! [X59,X60] :
      ( ~ m1_subset_1(X59,X60)
      | v1_xboole_0(X60)
      | r2_hidden(X59,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_14,plain,(
    ! [X29] : m1_subset_1(esk9_1(X29),X29) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_15,plain,
    ( v3_pre_topc(esk11_4(X1,X2,X3,X4),X2)
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_16,negated_conjecture,
    ( u1_struct_0(esk2_0) = u1_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_17,negated_conjecture,
    ( l1_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( v2_pre_topc(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk3_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk3_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk11_4(X1,X2,X3,X4),k1_zfmisc_1(u1_struct_0(X2)))
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

fof(c_0_23,plain,(
    ! [X71,X72,X73] :
      ( ~ r2_hidden(X71,X72)
      | ~ m1_subset_1(X72,k1_zfmisc_1(X73))
      | m1_subset_1(X71,X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_24,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_25,plain,
    ( m1_subset_1(esk9_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_26,plain,(
    ! [X61,X62] :
      ( ( ~ m1_subset_1(X61,k1_zfmisc_1(X62))
        | r1_tarski(X61,X62) )
      & ( ~ r1_tarski(X61,X62)
        | m1_subset_1(X61,k1_zfmisc_1(X62)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_27,plain,(
    ! [X74,X75,X76] :
      ( ~ r2_hidden(X74,X75)
      | ~ m1_subset_1(X75,k1_zfmisc_1(X76))
      | ~ v1_xboole_0(X76) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_28,negated_conjecture,
    ( v3_pre_topc(esk11_4(X1,esk3_0,X2,X3),esk3_0)
    | r1_tmap_1(X1,esk3_0,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_15,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( v1_funct_2(esk5_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_20,c_0_16])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(rw,[status(thm)],[c_0_21,c_0_16])).

cnf(c_0_31,negated_conjecture,
    ( v1_funct_1(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_32,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_33,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_34,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_35,negated_conjecture,
    ( r1_tmap_1(X1,esk3_0,X2,X3)
    | m1_subset_1(esk11_4(X1,esk3_0,X2,X3),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | r2_hidden(esk9_1(X1),X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_38,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_39,negated_conjecture,
    ( r1_tarski(u1_pre_topc(esk3_0),u1_pre_topc(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_40,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_41,plain,(
    ! [X15,X16] :
      ( ( ~ v3_pre_topc(X16,X15)
        | r2_hidden(X16,u1_pre_topc(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) )
      & ( ~ r2_hidden(X16,u1_pre_topc(X15))
        | v3_pre_topc(X16,X15)
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ l1_pre_topc(X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d5_pre_topc])])])])).

cnf(c_0_42,negated_conjecture,
    ( v3_pre_topc(esk11_4(esk1_0,esk3_0,esk5_0,X1),esk3_0)
    | r1_tmap_1(esk1_0,esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_28,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_43,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_44,negated_conjecture,
    ( ~ r1_tmap_1(esk1_0,esk3_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_45,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk3_0,esk5_0,X1)
    | m1_subset_1(esk11_4(esk1_0,esk3_0,esk5_0,X1),k1_zfmisc_1(u1_struct_0(esk2_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_46,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(esk9_1(X1),X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_47,negated_conjecture,
    ( m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(u1_pre_topc(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_48,plain,
    ( v1_xboole_0(X1)
    | ~ v1_xboole_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_37])).

fof(c_0_49,plain,(
    ! [X78,X79] :
      ( ~ r2_hidden(X78,X79)
      | ~ v1_xboole_0(X79) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_50,plain,
    ( r2_hidden(X1,u1_pre_topc(X2))
    | ~ v3_pre_topc(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_51,negated_conjecture,
    ( v3_pre_topc(esk11_4(esk1_0,esk3_0,esk5_0,esk6_0),esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_44])).

cnf(c_0_52,negated_conjecture,
    ( m1_subset_1(esk11_4(esk1_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_43]),c_0_44])).

cnf(c_0_53,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk3_0))
    | m1_subset_1(esk9_1(u1_pre_topc(esk3_0)),u1_pre_topc(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk3_0))
    | ~ v1_xboole_0(u1_pre_topc(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_47])).

cnf(c_0_55,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r2_hidden(esk11_4(esk1_0,esk3_0,esk5_0,esk6_0),u1_pre_topc(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_16]),c_0_52]),c_0_17])])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(u1_pre_topc(esk3_0))
    | r2_hidden(esk9_1(u1_pre_topc(esk3_0)),u1_pre_topc(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_53]),c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( ~ v1_xboole_0(u1_pre_topc(esk3_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_59,plain,
    ( r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),esk11_4(X1,X2,X3,X4))
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(esk11_4(esk1_0,esk3_0,esk5_0,esk6_0),X1)
    | ~ m1_subset_1(u1_pre_topc(esk3_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_36,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk9_1(u1_pre_topc(esk3_0)),u1_pre_topc(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),esk11_4(X1,esk3_0,X2,X3))
    | r1_tmap_1(X1,esk3_0,X2,X3)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_63,negated_conjecture,
    ( m1_subset_1(esk11_4(esk1_0,esk3_0,esk5_0,esk6_0),u1_pre_topc(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_60,c_0_47])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(u1_pre_topc(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_61])).

fof(c_0_65,plain,(
    ! [X39,X40,X41,X42,X43,X44] :
      ( ( ~ r1_funct_2(X39,X40,X41,X42,X43,X44)
        | X43 = X44
        | v1_xboole_0(X40)
        | v1_xboole_0(X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X39,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X41,X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) )
      & ( X43 != X44
        | r1_funct_2(X39,X40,X41,X42,X43,X44)
        | v1_xboole_0(X40)
        | v1_xboole_0(X42)
        | ~ v1_funct_1(X43)
        | ~ v1_funct_2(X43,X39,X40)
        | ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X39,X40)))
        | ~ v1_funct_1(X44)
        | ~ v1_funct_2(X44,X41,X42)
        | ~ m1_subset_1(X44,k1_zfmisc_1(k2_zfmisc_1(X41,X42))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_funct_2])])])])).

cnf(c_0_66,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk3_0),esk4_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_67,negated_conjecture,
    ( r2_hidden(k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,X1),esk11_4(esk1_0,esk3_0,esk5_0,X1))
    | r1_tmap_1(esk1_0,esk3_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_29]),c_0_30]),c_0_31]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_68,plain,
    ( v3_pre_topc(X1,X2)
    | ~ r2_hidden(X1,u1_pre_topc(X2))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk11_4(esk1_0,esk3_0,esk5_0,esk6_0),u1_pre_topc(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_63]),c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( l1_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_71,plain,
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
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,negated_conjecture,
    ( r1_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0,esk5_0) ),
    inference(rw,[status(thm)],[c_0_66,c_0_16])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk4_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_74,negated_conjecture,
    ( v1_funct_2(esk4_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_75,negated_conjecture,
    ( v1_funct_1(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk5_0,esk6_0),esk11_4(esk1_0,esk3_0,esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_43]),c_0_44])).

cnf(c_0_77,negated_conjecture,
    ( v3_pre_topc(esk11_4(esk1_0,esk3_0,esk5_0,esk6_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_52]),c_0_70])])).

cnf(c_0_78,negated_conjecture,
    ( esk5_0 = esk4_0
    | v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_30]),c_0_73]),c_0_29]),c_0_74]),c_0_31]),c_0_75])])).

cnf(c_0_79,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(esk11_4(esk1_0,esk3_0,esk5_0,esk6_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_40,c_0_76])).

cnf(c_0_80,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | v3_pre_topc(esk11_4(esk1_0,esk3_0,esk4_0,esk6_0),esk2_0) ),
    inference(spm,[status(thm)],[c_0_77,c_0_78])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_79,c_0_52])).

cnf(c_0_82,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | m1_subset_1(esk11_4(esk1_0,esk3_0,esk4_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(spm,[status(thm)],[c_0_52,c_0_78])).

cnf(c_0_83,plain,
    ( r1_tmap_1(X2,X4,X5,X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_pre_topc(X1,X2)
    | ~ r2_hidden(X3,X1)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X2),u1_struct_0(X4),X5,X1),esk11_4(X2,X4,X5,X3))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X4))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
    | ~ v2_pre_topc(X4)
    | ~ l1_pre_topc(X4)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_84,plain,
    ( r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,esk10_5(X1,X2,X3,X4,X5)),X5)
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_85,negated_conjecture,
    ( v3_pre_topc(esk11_4(esk1_0,esk3_0,esk4_0,esk6_0),esk2_0) ),
    inference(sr,[status(thm)],[c_0_80,c_0_81])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(esk11_4(esk1_0,esk3_0,esk4_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk2_0))) ),
    inference(sr,[status(thm)],[c_0_82,c_0_81])).

cnf(c_0_87,negated_conjecture,
    ( v2_pre_topc(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_88,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_89,negated_conjecture,
    ( esk5_0 = esk4_0 ),
    inference(sr,[status(thm)],[c_0_78,c_0_81])).

cnf(c_0_90,plain,
    ( v3_pre_topc(esk10_5(X1,X2,X3,X4,X5),X1)
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_91,plain,
    ( r2_hidden(X1,esk10_5(X2,X3,X4,X1,X5))
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_92,plain,
    ( m1_subset_1(esk10_5(X1,X2,X3,X4,X5),k1_zfmisc_1(u1_struct_0(X1)))
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
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_93,plain,
    ( r1_tmap_1(X1,X2,X3,X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ v3_pre_topc(X5,X1)
    | ~ r2_hidden(X4,X5)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3,X5),esk11_4(X1,X2,X3,X4))
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[c_0_83,c_0_36])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,esk10_5(X1,esk2_0,X2,X3,esk11_4(esk1_0,esk3_0,esk4_0,esk6_0))),esk11_4(esk1_0,esk3_0,esk4_0,esk6_0))
    | v2_struct_0(X1)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),esk11_4(esk1_0,esk3_0,esk4_0,esk6_0))
    | ~ r1_tmap_1(X1,esk2_0,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_86]),c_0_70]),c_0_87])]),c_0_88])).

cnf(c_0_95,negated_conjecture,
    ( r1_tmap_1(esk1_0,esk2_0,esk4_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(k3_funct_2(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0,esk6_0),esk11_4(esk1_0,esk3_0,esk4_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_76,c_0_89]),c_0_89])).

cnf(c_0_97,negated_conjecture,
    ( v3_pre_topc(esk10_5(X1,esk2_0,X2,X3,esk11_4(esk1_0,esk3_0,esk4_0,esk6_0)),X1)
    | v2_struct_0(X1)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),esk11_4(esk1_0,esk3_0,esk4_0,esk6_0))
    | ~ r1_tmap_1(X1,esk2_0,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_85]),c_0_86]),c_0_70]),c_0_87])]),c_0_88])).

cnf(c_0_98,negated_conjecture,
    ( r2_hidden(X1,esk10_5(X2,esk2_0,X3,X1,esk11_4(esk1_0,esk3_0,esk4_0,esk6_0)))
    | v2_struct_0(X2)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X2),u1_struct_0(esk2_0),X3,X1),esk11_4(esk1_0,esk3_0,esk4_0,esk6_0))
    | ~ r1_tmap_1(X2,esk2_0,X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X3)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_85]),c_0_86]),c_0_70]),c_0_87])]),c_0_88])).

cnf(c_0_99,negated_conjecture,
    ( m1_subset_1(esk10_5(X1,esk2_0,X2,X3,esk11_4(esk1_0,esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ r2_hidden(k3_funct_2(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X3),esk11_4(esk1_0,esk3_0,esk4_0,esk6_0))
    | ~ r1_tmap_1(X1,esk2_0,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_85]),c_0_86]),c_0_70]),c_0_87])]),c_0_88])).

cnf(c_0_100,negated_conjecture,
    ( r1_tmap_1(X1,esk3_0,X2,X3)
    | v2_struct_0(X1)
    | ~ v3_pre_topc(X4,X1)
    | ~ r2_hidden(X3,X4)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk2_0))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk2_0))
    | ~ v1_funct_1(X2)
    | ~ r1_tarski(k7_relset_1(u1_struct_0(X1),u1_struct_0(esk2_0),X2,X4),esk11_4(X1,esk3_0,X2,X3))
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_16]),c_0_17]),c_0_18])]),c_0_19])).

cnf(c_0_101,negated_conjecture,
    ( r1_tarski(k7_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk4_0,esk10_5(esk1_0,esk2_0,esk4_0,esk6_0,esk11_4(esk1_0,esk3_0,esk4_0,esk6_0))),esk11_4(esk1_0,esk3_0,esk4_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_96]),c_0_73]),c_0_43]),c_0_74]),c_0_75]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_102,negated_conjecture,
    ( v3_pre_topc(esk10_5(esk1_0,esk2_0,esk4_0,esk6_0,esk11_4(esk1_0,esk3_0,esk4_0,esk6_0)),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_95]),c_0_96]),c_0_73]),c_0_43]),c_0_74]),c_0_75]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_103,negated_conjecture,
    ( r2_hidden(esk6_0,esk10_5(esk1_0,esk2_0,esk4_0,esk6_0,esk11_4(esk1_0,esk3_0,esk4_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_98,c_0_95]),c_0_96]),c_0_73]),c_0_43]),c_0_74]),c_0_75]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk10_5(esk1_0,esk2_0,esk4_0,esk6_0,esk11_4(esk1_0,esk3_0,esk4_0,esk6_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_99,c_0_95]),c_0_96]),c_0_73]),c_0_43]),c_0_74]),c_0_75]),c_0_32]),c_0_33])]),c_0_34])).

cnf(c_0_105,negated_conjecture,
    ( ~ r1_tmap_1(esk1_0,esk3_0,esk4_0,esk6_0) ),
    inference(rw,[status(thm)],[c_0_44,c_0_89])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102]),c_0_103]),c_0_73]),c_0_104]),c_0_74]),c_0_75]),c_0_32]),c_0_33])]),c_0_105]),c_0_34]),
    [proof]).
%------------------------------------------------------------------------------
