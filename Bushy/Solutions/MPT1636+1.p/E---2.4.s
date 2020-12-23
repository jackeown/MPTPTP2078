%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t16_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:45 EDT 2019

% Result     : Theorem 169.44s
% Output     : CNFRefutation 169.44s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 197 expanded)
%              Number of clauses        :   38 (  80 expanded)
%              Number of leaves         :   14 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  354 ( 840 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   21 (   6 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t16_waybel_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r1_tarski(X2,k3_waybel_0(X1,X2))
            & r1_tarski(X2,k4_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',t16_waybel_0)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',cc1_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',dt_u1_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',t4_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',t5_subset)).

fof(d15_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k3_waybel_0(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                          & r1_orders_2(X1,X4,X5)
                          & r2_hidden(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',d15_waybel_0)).

fof(dt_k3_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k3_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',dt_k3_waybel_0)).

fof(d1_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_relat_2(X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(k4_tarski(X3,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',d1_relat_2)).

fof(d4_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_orders_2(X1)
      <=> r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',d4_orders_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',t2_subset)).

fof(d16_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
             => ( X3 = k4_waybel_0(X1,X2)
              <=> ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( r2_hidden(X4,X3)
                    <=> ? [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                          & r1_orders_2(X1,X5,X4)
                          & r2_hidden(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',d16_waybel_0)).

fof(dt_k4_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',dt_k4_waybel_0)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',d9_orders_2)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t16_waybel_0.p',d3_tarski)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r1_tarski(X2,k3_waybel_0(X1,X2))
              & r1_tarski(X2,k4_waybel_0(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_waybel_0])).

fof(c_0_15,plain,(
    ! [X10,X11,X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | v1_relat_1(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_16,plain,(
    ! [X51] :
      ( ~ l1_orders_2(X51)
      | m1_subset_1(u1_orders_2(X51),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X51),u1_struct_0(X51)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_17,plain,(
    ! [X62,X63,X64] :
      ( ~ r2_hidden(X62,X63)
      | ~ m1_subset_1(X63,k1_zfmisc_1(X64))
      | m1_subset_1(X62,X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_18,negated_conjecture,
    ( v3_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
    & ( ~ r1_tarski(esk2_0,k3_waybel_0(esk1_0,esk2_0))
      | ~ r1_tarski(esk2_0,k4_waybel_0(esk1_0,esk2_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_14])])])).

fof(c_0_19,plain,(
    ! [X65,X66,X67] :
      ( ~ r2_hidden(X65,X66)
      | ~ m1_subset_1(X66,k1_zfmisc_1(X67))
      | ~ v1_xboole_0(X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_20,plain,(
    ! [X13,X14,X15,X16,X18,X20] :
      ( ( m1_subset_1(esk3_4(X13,X14,X15,X16),u1_struct_0(X13))
        | ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | X15 != k3_waybel_0(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( r1_orders_2(X13,X16,esk3_4(X13,X14,X15,X16))
        | ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | X15 != k3_waybel_0(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( r2_hidden(esk3_4(X13,X14,X15,X16),X14)
        | ~ r2_hidden(X16,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | X15 != k3_waybel_0(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( ~ m1_subset_1(X18,u1_struct_0(X13))
        | ~ r1_orders_2(X13,X16,X18)
        | ~ r2_hidden(X18,X14)
        | r2_hidden(X16,X15)
        | ~ m1_subset_1(X16,u1_struct_0(X13))
        | X15 != k3_waybel_0(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk4_3(X13,X14,X15),u1_struct_0(X13))
        | X15 = k3_waybel_0(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( ~ r2_hidden(esk4_3(X13,X14,X15),X15)
        | ~ m1_subset_1(X20,u1_struct_0(X13))
        | ~ r1_orders_2(X13,esk4_3(X13,X14,X15),X20)
        | ~ r2_hidden(X20,X14)
        | X15 = k3_waybel_0(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( m1_subset_1(esk5_3(X13,X14,X15),u1_struct_0(X13))
        | r2_hidden(esk4_3(X13,X14,X15),X15)
        | X15 = k3_waybel_0(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( r1_orders_2(X13,esk4_3(X13,X14,X15),esk5_3(X13,X14,X15))
        | r2_hidden(esk4_3(X13,X14,X15),X15)
        | X15 = k3_waybel_0(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( r2_hidden(esk5_3(X13,X14,X15),X14)
        | r2_hidden(esk4_3(X13,X14,X15),X15)
        | X15 = k3_waybel_0(X13,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_waybel_0])])])])])).

fof(c_0_21,plain,(
    ! [X46,X47] :
      ( ~ l1_orders_2(X46)
      | ~ m1_subset_1(X47,k1_zfmisc_1(u1_struct_0(X46)))
      | m1_subset_1(k3_waybel_0(X46,X47),k1_zfmisc_1(u1_struct_0(X46))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_waybel_0])])).

fof(c_0_22,plain,(
    ! [X31,X32,X33,X34] :
      ( ( ~ r1_relat_2(X31,X32)
        | ~ r2_hidden(X33,X32)
        | r2_hidden(k4_tarski(X33,X33),X31)
        | ~ v1_relat_1(X31) )
      & ( r2_hidden(esk9_2(X31,X34),X34)
        | r1_relat_2(X31,X34)
        | ~ v1_relat_1(X31) )
      & ( ~ r2_hidden(k4_tarski(esk9_2(X31,X34),esk9_2(X31,X34)),X31)
        | r1_relat_2(X31,X34)
        | ~ v1_relat_1(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).

fof(c_0_23,plain,(
    ! [X42] :
      ( ( ~ v3_orders_2(X42)
        | r1_relat_2(u1_orders_2(X42),u1_struct_0(X42))
        | ~ l1_orders_2(X42) )
      & ( ~ r1_relat_2(u1_orders_2(X42),u1_struct_0(X42))
        | v3_orders_2(X42)
        | ~ l1_orders_2(X42) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).

cnf(c_0_24,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_25,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_26,plain,(
    ! [X58,X59] :
      ( ~ m1_subset_1(X58,X59)
      | v1_xboole_0(X59)
      | r2_hidden(X58,X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_27,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_30,plain,
    ( r2_hidden(X3,X5)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X5 != k3_waybel_0(X2,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_31,plain,
    ( m1_subset_1(k3_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_32,plain,
    ( r2_hidden(k4_tarski(X3,X3),X1)
    | ~ r1_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_33,plain,
    ( r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_34,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_24,c_0_25])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_29,c_0_28])).

fof(c_0_38,plain,(
    ! [X22,X23,X24,X25,X27,X29] :
      ( ( m1_subset_1(esk6_4(X22,X23,X24,X25),u1_struct_0(X22))
        | ~ r2_hidden(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | X24 != k4_waybel_0(X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,esk6_4(X22,X23,X24,X25),X25)
        | ~ r2_hidden(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | X24 != k4_waybel_0(X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk6_4(X22,X23,X24,X25),X23)
        | ~ r2_hidden(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | X24 != k4_waybel_0(X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( ~ m1_subset_1(X27,u1_struct_0(X22))
        | ~ r1_orders_2(X22,X27,X25)
        | ~ r2_hidden(X27,X23)
        | r2_hidden(X25,X24)
        | ~ m1_subset_1(X25,u1_struct_0(X22))
        | X24 != k4_waybel_0(X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk7_3(X22,X23,X24),u1_struct_0(X22))
        | X24 = k4_waybel_0(X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( ~ r2_hidden(esk7_3(X22,X23,X24),X24)
        | ~ m1_subset_1(X29,u1_struct_0(X22))
        | ~ r1_orders_2(X22,X29,esk7_3(X22,X23,X24))
        | ~ r2_hidden(X29,X23)
        | X24 = k4_waybel_0(X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( m1_subset_1(esk8_3(X22,X23,X24),u1_struct_0(X22))
        | r2_hidden(esk7_3(X22,X23,X24),X24)
        | X24 = k4_waybel_0(X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( r1_orders_2(X22,esk8_3(X22,X23,X24),esk7_3(X22,X23,X24))
        | r2_hidden(esk7_3(X22,X23,X24),X24)
        | X24 = k4_waybel_0(X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) )
      & ( r2_hidden(esk8_3(X22,X23,X24),X23)
        | r2_hidden(esk7_3(X22,X23,X24),X24)
        | X24 = k4_waybel_0(X22,X23)
        | ~ m1_subset_1(X24,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
        | ~ l1_orders_2(X22) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_waybel_0])])])])])).

fof(c_0_39,plain,(
    ! [X48,X49] :
      ( ~ l1_orders_2(X48)
      | ~ m1_subset_1(X49,k1_zfmisc_1(u1_struct_0(X48)))
      | m1_subset_1(k4_waybel_0(X48,X49),k1_zfmisc_1(u1_struct_0(X48))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_waybel_0])])).

cnf(c_0_40,plain,
    ( r2_hidden(X1,k3_waybel_0(X2,X3))
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_30,c_0_27])]),c_0_31])).

cnf(c_0_41,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_42,plain,(
    ! [X43,X44,X45] :
      ( ( ~ r1_orders_2(X43,X44,X45)
        | r2_hidden(k4_tarski(X44,X45),u1_orders_2(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ l1_orders_2(X43) )
      & ( ~ r2_hidden(k4_tarski(X44,X45),u1_orders_2(X43))
        | r1_orders_2(X43,X44,X45)
        | ~ m1_subset_1(X45,u1_struct_0(X43))
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ l1_orders_2(X43) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_43,plain,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(X2))
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2)
    | ~ v3_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])).

cnf(c_0_44,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_36]),c_0_37])).

cnf(c_0_45,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_46,plain,
    ( r2_hidden(X3,X5)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X5 != k4_waybel_0(X2,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_48,negated_conjecture,
    ( r2_hidden(X1,k3_waybel_0(esk1_0,esk2_0))
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_28]),c_0_41])])).

cnf(c_0_49,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_50,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_44]),c_0_41]),c_0_45])])).

cnf(c_0_51,plain,
    ( r2_hidden(X1,k4_waybel_0(X2,X3))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_46,c_0_27])]),c_0_47])).

fof(c_0_52,plain,(
    ! [X36,X37,X38,X39,X40] :
      ( ( ~ r1_tarski(X36,X37)
        | ~ r2_hidden(X38,X36)
        | r2_hidden(X38,X37) )
      & ( r2_hidden(esk10_2(X39,X40),X39)
        | r1_tarski(X39,X40) )
      & ( ~ r2_hidden(esk10_2(X39,X40),X40)
        | r1_tarski(X39,X40) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(X1,k3_waybel_0(esk1_0,esk2_0))
    | ~ r1_orders_2(esk1_0,X1,X2)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_36])).

cnf(c_0_54,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_50]),c_0_41])]),c_0_36])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,k4_waybel_0(esk1_0,esk2_0))
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_28]),c_0_41])])).

cnf(c_0_56,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk10_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(X1,k3_waybel_0(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_58,negated_conjecture,
    ( r2_hidden(X1,k4_waybel_0(esk1_0,esk2_0))
    | ~ r1_orders_2(esk1_0,X2,X1)
    | ~ r2_hidden(X2,esk2_0)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_55,c_0_36])).

cnf(c_0_59,negated_conjecture,
    ( r1_tarski(X1,k3_waybel_0(esk1_0,esk2_0))
    | ~ r2_hidden(esk10_2(X1,k3_waybel_0(esk1_0,esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_60,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(X1,k4_waybel_0(esk1_0,esk2_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_54])).

cnf(c_0_62,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k3_waybel_0(esk1_0,esk2_0))
    | ~ r1_tarski(esk2_0,k4_waybel_0(esk1_0,esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_63,negated_conjecture,
    ( r1_tarski(esk2_0,k3_waybel_0(esk1_0,esk2_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(X1,k4_waybel_0(esk1_0,esk2_0))
    | ~ r2_hidden(esk10_2(X1,k4_waybel_0(esk1_0,esk2_0)),esk2_0) ),
    inference(spm,[status(thm)],[c_0_56,c_0_61])).

cnf(c_0_65,negated_conjecture,
    ( ~ r1_tarski(esk2_0,k4_waybel_0(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_62,c_0_63])])).

cnf(c_0_66,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_60]),c_0_65]),
    [proof]).
%------------------------------------------------------------------------------
