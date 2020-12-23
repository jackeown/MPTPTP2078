%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1636+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:29 EST 2020

% Result     : Theorem 0.18s
% Output     : CNFRefutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 407 expanded)
%              Number of clauses        :   62 ( 174 expanded)
%              Number of leaves         :   14 ( 101 expanded)
%              Depth                    :   16
%              Number of atoms          :  417 (1645 expanded)
%              Number of equality atoms :   22 (  33 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   61 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(dt_k3_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k3_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_waybel_0)).

fof(t16_waybel_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( r1_tarski(X2,k3_waybel_0(X1,X2))
            & r1_tarski(X2,k4_waybel_0(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_waybel_0)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(d1_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_relat_2(X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(k4_tarski(X3,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_2)).

fof(d4_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_orders_2(X1)
      <=> r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_waybel_0)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_waybel_0)).

fof(dt_k4_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_waybel_0)).

fof(c_0_14,plain,(
    ! [X49,X50,X51] :
      ( ~ r2_hidden(X49,X50)
      | ~ m1_subset_1(X50,k1_zfmisc_1(X51))
      | m1_subset_1(X49,X51) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_15,plain,(
    ! [X42,X43] :
      ( ~ l1_orders_2(X42)
      | ~ m1_subset_1(X43,k1_zfmisc_1(u1_struct_0(X42)))
      | m1_subset_1(k3_waybel_0(X42,X43),k1_zfmisc_1(u1_struct_0(X42))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_waybel_0])])).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ( r1_tarski(X2,k3_waybel_0(X1,X2))
              & r1_tarski(X2,k4_waybel_0(X1,X2)) ) ) ) ),
    inference(assume_negation,[status(cth)],[t16_waybel_0])).

cnf(c_0_17,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,plain,
    ( m1_subset_1(k3_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_19,negated_conjecture,
    ( v3_orders_2(esk9_0)
    & l1_orders_2(esk9_0)
    & m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0)))
    & ( ~ r1_tarski(esk10_0,k3_waybel_0(esk9_0,esk10_0))
      | ~ r1_tarski(esk10_0,k4_waybel_0(esk9_0,esk10_0)) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

cnf(c_0_20,plain,
    ( m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,k3_waybel_0(X2,X3))
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( m1_subset_1(esk10_0,k1_zfmisc_1(u1_struct_0(esk9_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_22,negated_conjecture,
    ( l1_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_23,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( ( ~ r1_tarski(X32,X33)
        | ~ r2_hidden(X34,X32)
        | r2_hidden(X34,X33) )
      & ( r2_hidden(esk8_2(X35,X36),X35)
        | r1_tarski(X35,X36) )
      & ( ~ r2_hidden(esk8_2(X35,X36),X36)
        | r1_tarski(X35,X36) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_24,plain,(
    ! [X47,X48] :
      ( ~ m1_subset_1(X47,X48)
      | v1_xboole_0(X48)
      | r2_hidden(X47,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ r2_hidden(X1,k3_waybel_0(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])])).

cnf(c_0_26,plain,
    ( r2_hidden(esk8_2(X1,X2),X1)
    | r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

fof(c_0_27,plain,(
    ! [X52,X53,X54] :
      ( ~ r2_hidden(X52,X53)
      | ~ m1_subset_1(X53,k1_zfmisc_1(X54))
      | ~ v1_xboole_0(X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

fof(c_0_28,plain,(
    ! [X6,X7,X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | v1_relat_1(X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

fof(c_0_29,plain,(
    ! [X46] :
      ( ~ l1_orders_2(X46)
      | m1_subset_1(u1_orders_2(X46),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),u1_struct_0(X46)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk9_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_17,c_0_21])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( r1_tarski(k3_waybel_0(esk9_0,esk10_0),X1)
    | m1_subset_1(esk8_2(k3_waybel_0(esk9_0,esk10_0),X1),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

cnf(c_0_33,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ r1_relat_2(X27,X28)
        | ~ r2_hidden(X29,X28)
        | r2_hidden(k4_tarski(X29,X29),X27)
        | ~ v1_relat_1(X27) )
      & ( r2_hidden(esk7_2(X27,X30),X30)
        | r1_relat_2(X27,X30)
        | ~ v1_relat_1(X27) )
      & ( ~ r2_hidden(k4_tarski(esk7_2(X27,X30),esk7_2(X27,X30)),X27)
        | r1_relat_2(X27,X30)
        | ~ v1_relat_1(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).

cnf(c_0_35,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_37,negated_conjecture,
    ( r1_tarski(esk10_0,X1)
    | m1_subset_1(esk8_2(esk10_0,X1),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_30,c_0_26])).

fof(c_0_38,plain,(
    ! [X38] :
      ( ( ~ v3_orders_2(X38)
        | r1_relat_2(u1_orders_2(X38),u1_struct_0(X38))
        | ~ l1_orders_2(X38) )
      & ( ~ r1_relat_2(u1_orders_2(X38),u1_struct_0(X38))
        | v3_orders_2(X38)
        | ~ l1_orders_2(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).

cnf(c_0_39,plain,
    ( r1_tarski(X1,X2)
    | ~ r2_hidden(esk8_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_40,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk9_0))
    | r1_tarski(k3_waybel_0(esk9_0,esk10_0),X1)
    | r2_hidden(esk8_2(k3_waybel_0(esk9_0,esk10_0),X1),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_41,plain,
    ( ~ v1_xboole_0(u1_struct_0(X1))
    | ~ r2_hidden(X2,k3_waybel_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(spm,[status(thm)],[c_0_33,c_0_18])).

cnf(c_0_42,plain,
    ( r2_hidden(esk7_2(X1,X2),X2)
    | r1_relat_2(X1,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_43,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk9_0))
    | r1_tarski(esk10_0,X1)
    | r2_hidden(esk8_2(esk10_0,X1),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_37])).

cnf(c_0_45,plain,
    ( r2_hidden(k4_tarski(X3,X3),X1)
    | ~ r1_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_46,plain,
    ( r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_47,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_48,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk9_0))
    | r1_tarski(k3_waybel_0(esk9_0,esk10_0),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_49,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk9_0))
    | ~ r2_hidden(X1,k3_waybel_0(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_21]),c_0_22])])).

cnf(c_0_50,plain,
    ( r1_relat_2(u1_orders_2(X1),X2)
    | r2_hidden(esk7_2(u1_orders_2(X1),X2),X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk9_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_21])).

cnf(c_0_52,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk9_0))
    | r1_tarski(esk10_0,u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_44])).

cnf(c_0_53,plain,
    ( r1_relat_2(X1,X2)
    | ~ r2_hidden(k4_tarski(esk7_2(X1,X2),esk7_2(X1,X2)),X1)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_54,plain,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(X2))
    | ~ v3_orders_2(X2)
    | ~ r2_hidden(X1,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_46]),c_0_43])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk9_0))
    | ~ r2_hidden(X1,k3_waybel_0(esk9_0,esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_48]),c_0_49])).

cnf(c_0_56,negated_conjecture,
    ( r1_relat_2(u1_orders_2(esk9_0),X1)
    | r2_hidden(esk7_2(u1_orders_2(esk9_0),X1),X1) ),
    inference(spm,[status(thm)],[c_0_50,c_0_22])).

fof(c_0_57,plain,(
    ! [X9,X10,X11,X12,X14,X16] :
      ( ( m1_subset_1(esk1_4(X9,X10,X11,X12),u1_struct_0(X9))
        | ~ r2_hidden(X12,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | X11 != k3_waybel_0(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( r1_orders_2(X9,X12,esk1_4(X9,X10,X11,X12))
        | ~ r2_hidden(X12,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | X11 != k3_waybel_0(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk1_4(X9,X10,X11,X12),X10)
        | ~ r2_hidden(X12,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | X11 != k3_waybel_0(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( ~ m1_subset_1(X14,u1_struct_0(X9))
        | ~ r1_orders_2(X9,X12,X14)
        | ~ r2_hidden(X14,X10)
        | r2_hidden(X12,X11)
        | ~ m1_subset_1(X12,u1_struct_0(X9))
        | X11 != k3_waybel_0(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk2_3(X9,X10,X11),u1_struct_0(X9))
        | X11 = k3_waybel_0(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( ~ r2_hidden(esk2_3(X9,X10,X11),X11)
        | ~ m1_subset_1(X16,u1_struct_0(X9))
        | ~ r1_orders_2(X9,esk2_3(X9,X10,X11),X16)
        | ~ r2_hidden(X16,X10)
        | X11 = k3_waybel_0(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( m1_subset_1(esk3_3(X9,X10,X11),u1_struct_0(X9))
        | r2_hidden(esk2_3(X9,X10,X11),X11)
        | X11 = k3_waybel_0(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( r1_orders_2(X9,esk2_3(X9,X10,X11),esk3_3(X9,X10,X11))
        | r2_hidden(esk2_3(X9,X10,X11),X11)
        | X11 = k3_waybel_0(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) )
      & ( r2_hidden(esk3_3(X9,X10,X11),X10)
        | r2_hidden(esk2_3(X9,X10,X11),X11)
        | X11 = k3_waybel_0(X9,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(X9)))
        | ~ l1_orders_2(X9) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d15_waybel_0])])])])])).

cnf(c_0_58,negated_conjecture,
    ( r1_tarski(esk10_0,u1_struct_0(esk9_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( r1_relat_2(u1_orders_2(X1),X2)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(esk7_2(u1_orders_2(X1),X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_54]),c_0_43])).

cnf(c_0_60,negated_conjecture,
    ( r1_relat_2(u1_orders_2(esk9_0),k3_waybel_0(esk9_0,esk10_0))
    | r2_hidden(esk7_2(u1_orders_2(esk9_0),k3_waybel_0(esk9_0,esk10_0)),u1_struct_0(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_56])).

cnf(c_0_61,negated_conjecture,
    ( v3_orders_2(esk9_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_62,plain,
    ( r2_hidden(X3,X5)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X5 != k3_waybel_0(X2,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_57])).

fof(c_0_63,plain,(
    ! [X39,X40,X41] :
      ( ( ~ r1_orders_2(X39,X40,X41)
        | r2_hidden(k4_tarski(X40,X41),u1_orders_2(X39))
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | ~ l1_orders_2(X39) )
      & ( ~ r2_hidden(k4_tarski(X40,X41),u1_orders_2(X39))
        | r1_orders_2(X39,X40,X41)
        | ~ m1_subset_1(X41,u1_struct_0(X39))
        | ~ m1_subset_1(X40,u1_struct_0(X39))
        | ~ l1_orders_2(X39) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk10_0,u1_struct_0(esk9_0))
    | r1_tarski(esk10_0,X1) ),
    inference(spm,[status(thm)],[c_0_58,c_0_26])).

fof(c_0_65,plain,(
    ! [X18,X19,X20,X21,X23,X25] :
      ( ( m1_subset_1(esk4_4(X18,X19,X20,X21),u1_struct_0(X18))
        | ~ r2_hidden(X21,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | X20 != k4_waybel_0(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,esk4_4(X18,X19,X20,X21),X21)
        | ~ r2_hidden(X21,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | X20 != k4_waybel_0(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( r2_hidden(esk4_4(X18,X19,X20,X21),X19)
        | ~ r2_hidden(X21,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | X20 != k4_waybel_0(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( ~ m1_subset_1(X23,u1_struct_0(X18))
        | ~ r1_orders_2(X18,X23,X21)
        | ~ r2_hidden(X23,X19)
        | r2_hidden(X21,X20)
        | ~ m1_subset_1(X21,u1_struct_0(X18))
        | X20 != k4_waybel_0(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk5_3(X18,X19,X20),u1_struct_0(X18))
        | X20 = k4_waybel_0(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( ~ r2_hidden(esk5_3(X18,X19,X20),X20)
        | ~ m1_subset_1(X25,u1_struct_0(X18))
        | ~ r1_orders_2(X18,X25,esk5_3(X18,X19,X20))
        | ~ r2_hidden(X25,X19)
        | X20 = k4_waybel_0(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( m1_subset_1(esk6_3(X18,X19,X20),u1_struct_0(X18))
        | r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k4_waybel_0(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( r1_orders_2(X18,esk6_3(X18,X19,X20),esk5_3(X18,X19,X20))
        | r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k4_waybel_0(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) )
      & ( r2_hidden(esk6_3(X18,X19,X20),X19)
        | r2_hidden(esk5_3(X18,X19,X20),X20)
        | X20 = k4_waybel_0(X18,X19)
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ m1_subset_1(X19,k1_zfmisc_1(u1_struct_0(X18)))
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d16_waybel_0])])])])])).

fof(c_0_66,plain,(
    ! [X44,X45] :
      ( ~ l1_orders_2(X44)
      | ~ m1_subset_1(X45,k1_zfmisc_1(u1_struct_0(X44)))
      | m1_subset_1(k4_waybel_0(X44,X45),k1_zfmisc_1(u1_struct_0(X44))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k4_waybel_0])])).

cnf(c_0_67,negated_conjecture,
    ( r1_relat_2(u1_orders_2(esk9_0),k3_waybel_0(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_61]),c_0_22])])).

cnf(c_0_68,plain,
    ( r2_hidden(X1,k3_waybel_0(X2,X3))
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r2_hidden(X4,X3)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_62,c_0_17])]),c_0_18])).

cnf(c_0_69,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r1_tarski(esk10_0,u1_struct_0(esk9_0)) ),
    inference(ef,[status(thm)],[c_0_64])).

cnf(c_0_71,plain,
    ( r2_hidden(X3,X5)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_orders_2(X2,X1,X3)
    | ~ r2_hidden(X1,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | X5 != k4_waybel_0(X2,X4)
    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( m1_subset_1(k4_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_73,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk9_0))
    | ~ r2_hidden(X1,k3_waybel_0(esk9_0,esk10_0))
    | ~ v1_relat_1(u1_orders_2(esk9_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_67])).

cnf(c_0_74,negated_conjecture,
    ( r2_hidden(X1,k3_waybel_0(esk9_0,esk10_0))
    | ~ r1_orders_2(esk9_0,X1,X2)
    | ~ r2_hidden(X2,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_21]),c_0_22])])).

cnf(c_0_75,plain,
    ( r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_69,c_0_54])).

cnf(c_0_76,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk9_0))
    | ~ r2_hidden(X1,esk10_0) ),
    inference(spm,[status(thm)],[c_0_47,c_0_70])).

cnf(c_0_77,plain,
    ( r2_hidden(X1,k4_waybel_0(X2,X3))
    | ~ r1_orders_2(X2,X4,X1)
    | ~ r2_hidden(X4,X3)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ m1_subset_1(X1,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_71,c_0_17])]),c_0_72])).

cnf(c_0_78,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,X1)
    | ~ r2_hidden(X1,k3_waybel_0(esk9_0,esk10_0))
    | ~ v1_relat_1(u1_orders_2(esk9_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_73]),c_0_22])]),c_0_25])).

cnf(c_0_79,negated_conjecture,
    ( r1_tarski(esk10_0,X1)
    | r2_hidden(esk8_2(esk10_0,X1),k3_waybel_0(esk9_0,esk10_0))
    | ~ r1_orders_2(esk9_0,esk8_2(esk10_0,X1),X2)
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_74,c_0_37])).

cnf(c_0_80,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,X1)
    | ~ r2_hidden(X1,esk10_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_61]),c_0_22])]),c_0_30])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(X1,k4_waybel_0(esk9_0,esk10_0))
    | ~ r1_orders_2(esk9_0,X2,X1)
    | ~ r2_hidden(X2,esk10_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk9_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_21]),c_0_22])])).

cnf(c_0_82,negated_conjecture,
    ( r1_orders_2(esk9_0,X1,X1)
    | ~ r2_hidden(X1,k3_waybel_0(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_43]),c_0_22])])).

cnf(c_0_83,negated_conjecture,
    ( r1_tarski(esk10_0,X1)
    | r2_hidden(esk8_2(esk10_0,X1),k3_waybel_0(esk9_0,esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_26])).

cnf(c_0_84,negated_conjecture,
    ( r1_tarski(esk10_0,X1)
    | r2_hidden(esk8_2(esk10_0,X1),k4_waybel_0(esk9_0,esk10_0))
    | ~ r1_orders_2(esk9_0,X2,esk8_2(esk10_0,X1))
    | ~ r2_hidden(X2,esk10_0) ),
    inference(spm,[status(thm)],[c_0_81,c_0_37])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk10_0,X1)
    | r1_orders_2(esk9_0,esk8_2(esk10_0,X1),esk8_2(esk10_0,X1)) ),
    inference(spm,[status(thm)],[c_0_82,c_0_83])).

cnf(c_0_86,negated_conjecture,
    ( ~ r1_tarski(esk10_0,k3_waybel_0(esk9_0,esk10_0))
    | ~ r1_tarski(esk10_0,k4_waybel_0(esk9_0,esk10_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_87,negated_conjecture,
    ( r1_tarski(esk10_0,k3_waybel_0(esk9_0,esk10_0)) ),
    inference(spm,[status(thm)],[c_0_39,c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( r1_tarski(esk10_0,X1)
    | r2_hidden(esk8_2(esk10_0,X1),k4_waybel_0(esk9_0,esk10_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_26])).

cnf(c_0_89,negated_conjecture,
    ( ~ r1_tarski(esk10_0,k4_waybel_0(esk9_0,esk10_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_86,c_0_87])])).

cnf(c_0_90,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_88]),c_0_89]),
    [proof]).

%------------------------------------------------------------------------------
