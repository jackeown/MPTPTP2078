%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t67_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:01 EDT 2019

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 469 expanded)
%              Number of clauses        :   43 ( 152 expanded)
%              Number of leaves         :   12 ( 118 expanded)
%              Depth                    :   12
%              Number of atoms          :  333 (4251 expanded)
%              Number of equality atoms :   57 ( 419 expanded)
%              Maximal formula depth    :   25 (   5 average)
%              Maximal clause size      :   88 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t67_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_orders_2(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v23_waybel_0(X3,X1,X2)
               => ( v1_funct_1(k2_funct_1(X3))
                  & v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1))
                  & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                  & k2_relat_1(k2_funct_1(X3)) = u1_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',t67_waybel_0)).

fof(t66_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & l1_orders_2(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( v23_waybel_0(X3,X1,X2)
              <=> ( v2_funct_1(X3)
                  & k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = u1_struct_0(X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( r1_orders_2(X1,X4,X5)
                          <=> r1_orders_2(X2,k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X4),k3_funct_2(u1_struct_0(X1),u1_struct_0(X2),X3,X5)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',t66_waybel_0)).

fof(t3_funct_2,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_funct_1(X1)
        & v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',t3_funct_2)).

fof(t55_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
       => ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
          & k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',t55_funct_1)).

fof(dt_k2_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',dt_k2_funct_1)).

fof(redefinition_k2_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k2_relset_1(X1,X2,X3) = k2_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',redefinition_k2_relset_1)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',cc1_relset_1)).

fof(d1_funct_2,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( ( ( X2 = k1_xboole_0
           => X1 = k1_xboole_0 )
         => ( v1_funct_2(X3,X1,X2)
          <=> X1 = k1_relset_1(X1,X2,X3) ) )
        & ( X2 = k1_xboole_0
         => ( X1 = k1_xboole_0
            | ( v1_funct_2(X3,X1,X2)
            <=> X3 = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',d1_funct_2)).

fof(redefinition_k1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => k1_relset_1(X1,X2,X3) = k1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',redefinition_k1_relset_1)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',dt_l1_orders_2)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t67_waybel_0.p',fc1_xboole_0)).

fof(c_0_12,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & l1_orders_2(X2) )
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( v23_waybel_0(X3,X1,X2)
                 => ( v1_funct_1(k2_funct_1(X3))
                    & v1_funct_2(k2_funct_1(X3),u1_struct_0(X2),u1_struct_0(X1))
                    & m1_subset_1(k2_funct_1(X3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                    & k2_relat_1(k2_funct_1(X3)) = u1_struct_0(X1) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t67_waybel_0])).

fof(c_0_13,plain,(
    ! [X62,X63,X64,X65,X66] :
      ( ( v2_funct_1(X64)
        | ~ v23_waybel_0(X64,X62,X63)
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63))))
        | v2_struct_0(X63)
        | ~ l1_orders_2(X63)
        | v2_struct_0(X62)
        | ~ l1_orders_2(X62) )
      & ( k2_relset_1(u1_struct_0(X62),u1_struct_0(X63),X64) = u1_struct_0(X63)
        | ~ v23_waybel_0(X64,X62,X63)
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63))))
        | v2_struct_0(X63)
        | ~ l1_orders_2(X63)
        | v2_struct_0(X62)
        | ~ l1_orders_2(X62) )
      & ( ~ r1_orders_2(X62,X65,X66)
        | r1_orders_2(X63,k3_funct_2(u1_struct_0(X62),u1_struct_0(X63),X64,X65),k3_funct_2(u1_struct_0(X62),u1_struct_0(X63),X64,X66))
        | ~ m1_subset_1(X66,u1_struct_0(X62))
        | ~ m1_subset_1(X65,u1_struct_0(X62))
        | ~ v23_waybel_0(X64,X62,X63)
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63))))
        | v2_struct_0(X63)
        | ~ l1_orders_2(X63)
        | v2_struct_0(X62)
        | ~ l1_orders_2(X62) )
      & ( ~ r1_orders_2(X63,k3_funct_2(u1_struct_0(X62),u1_struct_0(X63),X64,X65),k3_funct_2(u1_struct_0(X62),u1_struct_0(X63),X64,X66))
        | r1_orders_2(X62,X65,X66)
        | ~ m1_subset_1(X66,u1_struct_0(X62))
        | ~ m1_subset_1(X65,u1_struct_0(X62))
        | ~ v23_waybel_0(X64,X62,X63)
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63))))
        | v2_struct_0(X63)
        | ~ l1_orders_2(X63)
        | v2_struct_0(X62)
        | ~ l1_orders_2(X62) )
      & ( m1_subset_1(esk8_3(X62,X63,X64),u1_struct_0(X62))
        | ~ v2_funct_1(X64)
        | k2_relset_1(u1_struct_0(X62),u1_struct_0(X63),X64) != u1_struct_0(X63)
        | v23_waybel_0(X64,X62,X63)
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63))))
        | v2_struct_0(X63)
        | ~ l1_orders_2(X63)
        | v2_struct_0(X62)
        | ~ l1_orders_2(X62) )
      & ( m1_subset_1(esk9_3(X62,X63,X64),u1_struct_0(X62))
        | ~ v2_funct_1(X64)
        | k2_relset_1(u1_struct_0(X62),u1_struct_0(X63),X64) != u1_struct_0(X63)
        | v23_waybel_0(X64,X62,X63)
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63))))
        | v2_struct_0(X63)
        | ~ l1_orders_2(X63)
        | v2_struct_0(X62)
        | ~ l1_orders_2(X62) )
      & ( ~ r1_orders_2(X62,esk8_3(X62,X63,X64),esk9_3(X62,X63,X64))
        | ~ r1_orders_2(X63,k3_funct_2(u1_struct_0(X62),u1_struct_0(X63),X64,esk8_3(X62,X63,X64)),k3_funct_2(u1_struct_0(X62),u1_struct_0(X63),X64,esk9_3(X62,X63,X64)))
        | ~ v2_funct_1(X64)
        | k2_relset_1(u1_struct_0(X62),u1_struct_0(X63),X64) != u1_struct_0(X63)
        | v23_waybel_0(X64,X62,X63)
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63))))
        | v2_struct_0(X63)
        | ~ l1_orders_2(X63)
        | v2_struct_0(X62)
        | ~ l1_orders_2(X62) )
      & ( r1_orders_2(X62,esk8_3(X62,X63,X64),esk9_3(X62,X63,X64))
        | r1_orders_2(X63,k3_funct_2(u1_struct_0(X62),u1_struct_0(X63),X64,esk8_3(X62,X63,X64)),k3_funct_2(u1_struct_0(X62),u1_struct_0(X63),X64,esk9_3(X62,X63,X64)))
        | ~ v2_funct_1(X64)
        | k2_relset_1(u1_struct_0(X62),u1_struct_0(X63),X64) != u1_struct_0(X63)
        | v23_waybel_0(X64,X62,X63)
        | ~ v1_funct_1(X64)
        | ~ v1_funct_2(X64,u1_struct_0(X62),u1_struct_0(X63))
        | ~ m1_subset_1(X64,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X62),u1_struct_0(X63))))
        | v2_struct_0(X63)
        | ~ l1_orders_2(X63)
        | v2_struct_0(X62)
        | ~ l1_orders_2(X62) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t66_waybel_0])])])])])])).

fof(c_0_14,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & l1_orders_2(esk2_0)
    & v1_funct_1(esk3_0)
    & v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0))
    & m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0))))
    & v23_waybel_0(esk3_0,esk1_0,esk2_0)
    & ( ~ v1_funct_1(k2_funct_1(esk3_0))
      | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
      | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
      | k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_12])])])])).

fof(c_0_15,plain,(
    ! [X52] :
      ( ( v1_funct_1(X52)
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( v1_funct_2(X52,k1_relat_1(X52),k2_relat_1(X52))
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) )
      & ( m1_subset_1(X52,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X52),k2_relat_1(X52))))
        | ~ v1_relat_1(X52)
        | ~ v1_funct_1(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_funct_2])])])).

fof(c_0_16,plain,(
    ! [X58] :
      ( ( k2_relat_1(X58) = k1_relat_1(k2_funct_1(X58))
        | ~ v2_funct_1(X58)
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) )
      & ( k1_relat_1(X58) = k2_relat_1(k2_funct_1(X58))
        | ~ v2_funct_1(X58)
        | ~ v1_relat_1(X58)
        | ~ v1_funct_1(X58) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t55_funct_1])])])).

fof(c_0_17,plain,(
    ! [X22] :
      ( ( v1_relat_1(k2_funct_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) )
      & ( v1_funct_1(k2_funct_1(X22))
        | ~ v1_relat_1(X22)
        | ~ v1_funct_1(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_funct_1])])])).

fof(c_0_18,plain,(
    ! [X41,X42,X43] :
      ( ~ m1_subset_1(X43,k1_zfmisc_1(k2_zfmisc_1(X41,X42)))
      | k2_relset_1(X41,X42,X43) = k2_relat_1(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k2_relset_1])])).

cnf(c_0_19,plain,
    ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = u1_struct_0(X2)
    | v2_struct_0(X2)
    | v2_struct_0(X1)
    | ~ v23_waybel_0(X3,X1,X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_orders_2(X2)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_21,negated_conjecture,
    ( v23_waybel_0(esk3_0,esk1_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk3_0,u1_struct_0(esk1_0),u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_23,negated_conjecture,
    ( v1_funct_1(esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_25,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

fof(c_0_28,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | v1_relat_1(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),k2_relat_1(X1))))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_30,plain,
    ( k2_relat_1(X1) = k1_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_31,plain,
    ( v1_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_32,plain,
    ( v1_relat_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_33,plain,
    ( k2_relset_1(X2,X3,X1) = k2_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_34,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = u1_struct_0(esk2_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_35,plain,
    ( v2_funct_1(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ v23_waybel_0(X1,X2,X3)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,u1_struct_0(X2),u1_struct_0(X3))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X3))))
    | ~ l1_orders_2(X3)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_36,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_37,plain,(
    ! [X16,X17,X18] :
      ( ( ~ v1_funct_2(X18,X16,X17)
        | X16 = k1_relset_1(X16,X17,X18)
        | X17 = k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X16 != k1_relset_1(X16,X17,X18)
        | v1_funct_2(X18,X16,X17)
        | X17 = k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( ~ v1_funct_2(X18,X16,X17)
        | X16 = k1_relset_1(X16,X17,X18)
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X16 != k1_relset_1(X16,X17,X18)
        | v1_funct_2(X18,X16,X17)
        | X16 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( ~ v1_funct_2(X18,X16,X17)
        | X18 = k1_xboole_0
        | X16 = k1_xboole_0
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) )
      & ( X18 != k1_xboole_0
        | v1_funct_2(X18,X16,X17)
        | X16 = k1_xboole_0
        | X17 != k1_xboole_0
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_zfmisc_1(X16,X17))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_funct_2])])])).

cnf(c_0_38,plain,
    ( v1_funct_2(X1,k1_relat_1(X1),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_39,plain,
    ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_40,negated_conjecture,
    ( k2_relat_1(esk3_0) = u1_struct_0(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_34]),c_0_20])])).

cnf(c_0_41,negated_conjecture,
    ( v2_funct_1(esk3_0) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_20]),c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_25])]),c_0_26]),c_0_27])).

cnf(c_0_42,negated_conjecture,
    ( v1_relat_1(esk3_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_20])).

fof(c_0_43,plain,(
    ! [X38,X39,X40] :
      ( ~ m1_subset_1(X40,k1_zfmisc_1(k2_zfmisc_1(X38,X39)))
      | k1_relset_1(X38,X39,X40) = k1_relat_1(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k1_relset_1])])).

cnf(c_0_44,plain,
    ( X2 = k1_relset_1(X2,X3,X1)
    | X3 = k1_xboole_0
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_45,plain,
    ( v1_funct_2(k2_funct_1(X1),k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_30]),c_0_31]),c_0_32])).

cnf(c_0_46,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),k2_relat_1(k2_funct_1(esk3_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_41]),c_0_42]),c_0_23])])).

cnf(c_0_47,plain,
    ( k1_relat_1(X1) = k2_relat_1(k2_funct_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_48,plain,
    ( k1_relset_1(X2,X3,X1) = k1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_49,negated_conjecture,
    ( k1_relset_1(u1_struct_0(esk1_0),u1_struct_0(esk2_0),esk3_0) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_20]),c_0_22])])).

cnf(c_0_50,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),k2_relat_1(k2_funct_1(esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_40]),c_0_41]),c_0_42]),c_0_23])])).

cnf(c_0_51,negated_conjecture,
    ( m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),k1_relat_1(esk3_0)))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_47]),c_0_41]),c_0_42]),c_0_23])])).

cnf(c_0_52,negated_conjecture,
    ( k1_relat_1(esk3_0) = u1_struct_0(esk1_0)
    | u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_20])])).

cnf(c_0_53,negated_conjecture,
    ( v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),k1_relat_1(esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_47]),c_0_41]),c_0_42]),c_0_23])])).

cnf(c_0_54,negated_conjecture,
    ( ~ v1_funct_1(k2_funct_1(esk3_0))
    | ~ v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0))
    | ~ m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0))))
    | k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_55,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | m1_subset_1(k2_funct_1(esk3_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk2_0),u1_struct_0(esk1_0)))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_56,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(esk3_0),u1_struct_0(esk2_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_52])).

fof(c_0_57,plain,(
    ! [X35] :
      ( v2_struct_0(X35)
      | ~ l1_struct_0(X35)
      | ~ v1_xboole_0(u1_struct_0(X35)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_58,plain,(
    ! [X30] :
      ( ~ l1_orders_2(X30)
      | l1_struct_0(X30) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_59,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | k2_relat_1(k2_funct_1(esk3_0)) != u1_struct_0(esk1_0)
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_56])).

cnf(c_0_60,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

cnf(c_0_61,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_58])).

cnf(c_0_62,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0
    | ~ v1_funct_1(k2_funct_1(esk3_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_47]),c_0_41]),c_0_42]),c_0_23])]),c_0_52])).

cnf(c_0_63,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_60,c_0_61])).

cnf(c_0_64,negated_conjecture,
    ( u1_struct_0(esk2_0) = k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_31]),c_0_42]),c_0_23])])).

cnf(c_0_65,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_24])]),c_0_27]),
    [proof]).
%------------------------------------------------------------------------------
