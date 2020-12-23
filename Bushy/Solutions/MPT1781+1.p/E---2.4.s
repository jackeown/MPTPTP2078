%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : tmap_1__t96_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:23 EDT 2019

% Result     : Theorem 4.43s
% Output     : CNFRefutation 4.43s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 330 expanded)
%              Number of clauses        :   39 ( 103 expanded)
%              Number of leaves         :   11 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  351 (2897 expanded)
%              Number of equality atoms :   28 ( 213 expanded)
%              Maximal formula depth    :   24 (   6 average)
%              Maximal clause size      :   48 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t35_funct_1,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => k1_funct_1(k6_relat_1(X2),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t96_tmap_1.p',t35_funct_1)).

fof(redefinition_k6_partfun1,axiom,(
    ! [X1] : k6_partfun1(X1) = k6_relat_1(X1) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t96_tmap_1.p',redefinition_k6_partfun1)).

fof(t96_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,u1_struct_0(X2))
                     => X4 = k1_funct_1(X3,X4) ) )
               => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t96_tmap_1.p',t96_tmap_1)).

fof(t59_tmap_1,axiom,(
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
                & m1_pre_topc(X3,X2) )
             => ! [X4] :
                  ( ( v1_funct_1(X4)
                    & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
                 => ! [X5] :
                      ( ( v1_funct_1(X5)
                        & v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) )
                     => ( ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X2))
                           => ( r2_hidden(X6,u1_struct_0(X3))
                             => k3_funct_2(u1_struct_0(X2),u1_struct_0(X1),X4,X6) = k1_funct_1(X5,X6) ) )
                       => r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t96_tmap_1.p',t59_tmap_1)).

fof(redefinition_k3_funct_2,axiom,(
    ! [X1,X2,X3,X4] :
      ( ( ~ v1_xboole_0(X1)
        & v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & m1_subset_1(X4,X1) )
     => k3_funct_2(X1,X2,X3,X4) = k1_funct_1(X3,X4) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t96_tmap_1.p',redefinition_k3_funct_2)).

fof(d4_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k3_struct_0(X1) = k6_partfun1(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t96_tmap_1.p',d4_struct_0)).

fof(dt_k3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ( v1_funct_1(k3_struct_0(X1))
        & v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
        & m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t96_tmap_1.p',dt_k3_struct_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t96_tmap_1.p',t2_subset)).

fof(d7_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => k4_tmap_1(X1,X2) = k2_tmap_1(X1,X1,k3_struct_0(X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t96_tmap_1.p',d7_tmap_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t96_tmap_1.p',fc2_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t96_tmap_1.p',dt_l1_pre_topc)).

fof(c_0_11,plain,(
    ! [X69,X70] :
      ( ~ r2_hidden(X69,X70)
      | k1_funct_1(k6_relat_1(X70),X69) = X69 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t35_funct_1])])).

fof(c_0_12,plain,(
    ! [X52] : k6_partfun1(X52) = k6_relat_1(X52) ),
    inference(variable_rename,[status(thm)],[redefinition_k6_partfun1])).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & m1_pre_topc(X2,X1) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_hidden(X4,u1_struct_0(X2))
                       => X4 = k1_funct_1(X3,X4) ) )
                 => r2_funct_2(u1_struct_0(X2),u1_struct_0(X1),k4_tmap_1(X1,X2),X3) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t96_tmap_1])).

fof(c_0_14,plain,(
    ! [X76,X77,X78,X79,X80] :
      ( ( m1_subset_1(esk8_5(X76,X77,X78,X79,X80),u1_struct_0(X77))
        | r2_funct_2(u1_struct_0(X78),u1_struct_0(X76),k2_tmap_1(X77,X76,X79,X78),X80)
        | ~ v1_funct_1(X80)
        | ~ v1_funct_2(X80,u1_struct_0(X78),u1_struct_0(X76))
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),u1_struct_0(X76))))
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,u1_struct_0(X77),u1_struct_0(X76))
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X77),u1_struct_0(X76))))
        | v2_struct_0(X78)
        | ~ m1_pre_topc(X78,X77)
        | v2_struct_0(X77)
        | ~ v2_pre_topc(X77)
        | ~ l1_pre_topc(X77)
        | v2_struct_0(X76)
        | ~ v2_pre_topc(X76)
        | ~ l1_pre_topc(X76) )
      & ( r2_hidden(esk8_5(X76,X77,X78,X79,X80),u1_struct_0(X78))
        | r2_funct_2(u1_struct_0(X78),u1_struct_0(X76),k2_tmap_1(X77,X76,X79,X78),X80)
        | ~ v1_funct_1(X80)
        | ~ v1_funct_2(X80,u1_struct_0(X78),u1_struct_0(X76))
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),u1_struct_0(X76))))
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,u1_struct_0(X77),u1_struct_0(X76))
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X77),u1_struct_0(X76))))
        | v2_struct_0(X78)
        | ~ m1_pre_topc(X78,X77)
        | v2_struct_0(X77)
        | ~ v2_pre_topc(X77)
        | ~ l1_pre_topc(X77)
        | v2_struct_0(X76)
        | ~ v2_pre_topc(X76)
        | ~ l1_pre_topc(X76) )
      & ( k3_funct_2(u1_struct_0(X77),u1_struct_0(X76),X79,esk8_5(X76,X77,X78,X79,X80)) != k1_funct_1(X80,esk8_5(X76,X77,X78,X79,X80))
        | r2_funct_2(u1_struct_0(X78),u1_struct_0(X76),k2_tmap_1(X77,X76,X79,X78),X80)
        | ~ v1_funct_1(X80)
        | ~ v1_funct_2(X80,u1_struct_0(X78),u1_struct_0(X76))
        | ~ m1_subset_1(X80,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X78),u1_struct_0(X76))))
        | ~ v1_funct_1(X79)
        | ~ v1_funct_2(X79,u1_struct_0(X77),u1_struct_0(X76))
        | ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X77),u1_struct_0(X76))))
        | v2_struct_0(X78)
        | ~ m1_pre_topc(X78,X77)
        | v2_struct_0(X77)
        | ~ v2_pre_topc(X77)
        | ~ l1_pre_topc(X77)
        | v2_struct_0(X76)
        | ~ v2_pre_topc(X76)
        | ~ l1_pre_topc(X76) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t59_tmap_1])])])])])])).

fof(c_0_15,plain,(
    ! [X48,X49,X50,X51] :
      ( v1_xboole_0(X48)
      | ~ v1_funct_1(X50)
      | ~ v1_funct_2(X50,X48,X49)
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(X48,X49)))
      | ~ m1_subset_1(X51,X48)
      | k3_funct_2(X48,X49,X50,X51) = k1_funct_1(X50,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k3_funct_2])])])).

cnf(c_0_16,plain,
    ( k1_funct_1(k6_relat_1(X2),X1) = X1
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_17,plain,
    ( k6_partfun1(X1) = k6_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

fof(c_0_18,plain,(
    ! [X13] :
      ( ~ l1_struct_0(X13)
      | k3_struct_0(X13) = k6_partfun1(u1_struct_0(X13)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_struct_0])])).

fof(c_0_19,negated_conjecture,(
    ! [X10] :
      ( ~ v2_struct_0(esk1_0)
      & v2_pre_topc(esk1_0)
      & l1_pre_topc(esk1_0)
      & ~ v2_struct_0(esk2_0)
      & m1_pre_topc(esk2_0,esk1_0)
      & v1_funct_1(esk3_0)
      & v1_funct_2(esk3_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0))
      & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
      & ( ~ m1_subset_1(X10,u1_struct_0(esk1_0))
        | ~ r2_hidden(X10,u1_struct_0(esk2_0))
        | X10 = k1_funct_1(esk3_0,X10) )
      & ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk2_0),esk3_0) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).

cnf(c_0_20,plain,
    ( r2_funct_2(u1_struct_0(X4),u1_struct_0(X2),k2_tmap_1(X1,X2,X3,X4),X5)
    | v2_struct_0(X4)
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,esk8_5(X2,X1,X4,X3,X5)) != k1_funct_1(X5,esk8_5(X2,X1,X4,X3,X5))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X4),u1_struct_0(X2))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X2))))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ m1_pre_topc(X4,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,plain,
    ( v1_xboole_0(X1)
    | k3_funct_2(X1,X3,X2,X4) = k1_funct_1(X2,X4)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_2(X2,X1,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ m1_subset_1(X4,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk8_5(X1,X2,X3,X4,X5),u1_struct_0(X2))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,plain,
    ( k1_funct_1(k6_partfun1(X2),X1) = X1
    | ~ r2_hidden(X1,X2) ),
    inference(rw,[status(thm)],[c_0_16,c_0_17])).

cnf(c_0_24,plain,
    ( k3_struct_0(X1) = k6_partfun1(u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_25,plain,(
    ! [X28] :
      ( ( v1_funct_1(k3_struct_0(X28))
        | ~ l1_struct_0(X28) )
      & ( v1_funct_2(k3_struct_0(X28),u1_struct_0(X28),u1_struct_0(X28))
        | ~ l1_struct_0(X28) )
      & ( m1_subset_1(k3_struct_0(X28),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X28),u1_struct_0(X28))))
        | ~ l1_struct_0(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_struct_0])])])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_29,negated_conjecture,
    ( l1_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,negated_conjecture,
    ( v2_pre_topc(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_33,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X3),k2_tmap_1(X1,X3,X4,X2),X5)
    | v2_struct_0(X2)
    | v2_struct_0(X3)
    | v2_struct_0(X1)
    | k1_funct_1(X4,esk8_5(X3,X1,X2,X4,X5)) != k1_funct_1(X5,esk8_5(X3,X1,X2,X4,X5))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_2(X4,u1_struct_0(X1),u1_struct_0(X3))
    | ~ v1_funct_1(X5)
    | ~ v1_funct_1(X4)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])).

cnf(c_0_34,plain,
    ( k1_funct_1(k3_struct_0(X1),X2) = X2
    | ~ l1_struct_0(X1)
    | ~ r2_hidden(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_35,plain,
    ( v1_funct_1(k3_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_36,plain,(
    ! [X67,X68] :
      ( ~ m1_subset_1(X67,X68)
      | v1_xboole_0(X68)
      | r2_hidden(X67,X68) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_37,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tmap_1(X1,esk1_0,X2,esk2_0),esk3_0)
    | m1_subset_1(esk8_5(esk1_0,X1,esk2_0,X2,esk3_0),u1_struct_0(X1))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(esk1_0))))
    | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(esk1_0))
    | ~ v1_funct_1(X2)
    | ~ m1_pre_topc(esk2_0,X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_26]),c_0_27]),c_0_28]),c_0_29]),c_0_30])]),c_0_31]),c_0_32])).

cnf(c_0_38,plain,
    ( m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_39,negated_conjecture,
    ( m1_pre_topc(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_40,plain,
    ( v1_funct_2(k3_struct_0(X1),u1_struct_0(X1),u1_struct_0(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

fof(c_0_41,plain,(
    ! [X14,X15] :
      ( v2_struct_0(X14)
      | ~ v2_pre_topc(X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(X15,X14)
      | k4_tmap_1(X14,X15) = k2_tmap_1(X14,X14,k3_struct_0(X14),X15) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_tmap_1])])])])).

cnf(c_0_42,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_funct_2(u1_struct_0(X2),u1_struct_0(X3),k2_tmap_1(X1,X3,k3_struct_0(X4),X2),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | k1_funct_1(X5,esk8_5(X3,X1,X2,k3_struct_0(X4),X5)) != esk8_5(X3,X1,X2,k3_struct_0(X4),X5)
    | ~ l1_struct_0(X4)
    | ~ r2_hidden(esk8_5(X3,X1,X2,k3_struct_0(X4),X5),u1_struct_0(X4))
    | ~ m1_subset_1(k3_struct_0(X4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X3))))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ v1_funct_2(k3_struct_0(X4),u1_struct_0(X1),u1_struct_0(X3))
    | ~ v1_funct_2(X5,u1_struct_0(X2),u1_struct_0(X3))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_35])).

cnf(c_0_43,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tmap_1(esk1_0,esk1_0,k3_struct_0(esk1_0),esk2_0),esk3_0)
    | m1_subset_1(esk8_5(esk1_0,esk1_0,esk2_0,k3_struct_0(esk1_0),esk3_0),u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_39]),c_0_29]),c_0_30])]),c_0_31]),c_0_35]),c_0_40])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | k4_tmap_1(X1,X2) = k2_tmap_1(X1,X1,k3_struct_0(X1),X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_46,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k4_tmap_1(esk1_0,esk2_0),esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_47,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | v1_xboole_0(u1_struct_0(X2))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X4),k2_tmap_1(X2,X4,k3_struct_0(X1),X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X4)
    | v2_struct_0(X2)
    | k1_funct_1(X5,esk8_5(X4,X2,X3,k3_struct_0(X1),X5)) != esk8_5(X4,X2,X3,k3_struct_0(X1),X5)
    | ~ l1_struct_0(X1)
    | ~ m1_subset_1(k3_struct_0(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X4))))
    | ~ m1_subset_1(esk8_5(X4,X2,X3,k3_struct_0(X1),X5),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X4))))
    | ~ v1_funct_2(k3_struct_0(X1),u1_struct_0(X2),u1_struct_0(X4))
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X4))
    | ~ v1_funct_1(X5)
    | ~ m1_pre_topc(X3,X2)
    | ~ l1_pre_topc(X4)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X4)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_48,negated_conjecture,
    ( m1_subset_1(esk8_5(esk1_0,esk1_0,esk2_0,k3_struct_0(esk1_0),esk3_0),u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_39]),c_0_29]),c_0_30])]),c_0_46]),c_0_31])).

cnf(c_0_49,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tmap_1(esk1_0,esk1_0,k3_struct_0(esk1_0),esk2_0),esk3_0)
    | k1_funct_1(esk3_0,esk8_5(esk1_0,esk1_0,esk2_0,k3_struct_0(esk1_0),esk3_0)) != esk8_5(esk1_0,esk1_0,esk2_0,k3_struct_0(esk1_0),esk3_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_26]),c_0_27]),c_0_28]),c_0_39]),c_0_29]),c_0_30])]),c_0_32]),c_0_31]),c_0_40]),c_0_38])).

cnf(c_0_50,negated_conjecture,
    ( X1 = k1_funct_1(esk3_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_funct_2(u1_struct_0(esk2_0),u1_struct_0(esk1_0),k2_tmap_1(esk1_0,esk1_0,k3_struct_0(esk1_0),esk2_0),esk3_0)
    | ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(esk8_5(esk1_0,esk1_0,esk2_0,k3_struct_0(esk1_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_48])).

cnf(c_0_52,plain,
    ( r2_hidden(esk8_5(X1,X2,X3,X4,X5),u1_struct_0(X3))
    | r2_funct_2(u1_struct_0(X3),u1_struct_0(X1),k2_tmap_1(X2,X1,X4,X3),X5)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v1_funct_1(X5)
    | ~ v1_funct_2(X5,u1_struct_0(X3),u1_struct_0(X1))
    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
    | ~ v1_funct_1(X4)
    | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X3,X2)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_53,plain,(
    ! [X92] :
      ( v2_struct_0(X92)
      | ~ l1_struct_0(X92)
      | ~ v1_xboole_0(u1_struct_0(X92)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_54,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(esk8_5(esk1_0,esk1_0,esk2_0,k3_struct_0(esk1_0),esk3_0),u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_45]),c_0_39]),c_0_29]),c_0_30])]),c_0_46]),c_0_31])).

cnf(c_0_55,plain,
    ( r2_funct_2(u1_struct_0(X1),u1_struct_0(X2),k4_tmap_1(X2,X1),X3)
    | r2_hidden(esk8_5(X2,X2,X1,k3_struct_0(X2),X3),u1_struct_0(X1))
    | v2_struct_0(X1)
    | v2_struct_0(X2)
    | ~ m1_subset_1(k3_struct_0(X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2))))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ v1_funct_2(k3_struct_0(X2),u1_struct_0(X2),u1_struct_0(X2))
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_funct_1(k3_struct_0(X2))
    | ~ v1_funct_1(X3)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ v2_pre_topc(X2) ),
    inference(spm,[status(thm)],[c_0_52,c_0_45])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_57,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_26]),c_0_27]),c_0_28]),c_0_39]),c_0_29]),c_0_30])]),c_0_46]),c_0_32]),c_0_31]),c_0_35]),c_0_40]),c_0_38])).

fof(c_0_58,plain,(
    ! [X35] :
      ( ~ l1_pre_topc(X35)
      | l1_struct_0(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_59,negated_conjecture,
    ( ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_31])).

cnf(c_0_60,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_61,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
