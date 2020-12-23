%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t43_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:50 EDT 2019

% Result     : Theorem 174.73s
% Output     : CNFRefutation 174.73s
% Verified   : 
% Statistics : Number of formulae       :  107 (4051 expanded)
%              Number of clauses        :   78 (1462 expanded)
%              Number of leaves         :   14 ( 995 expanded)
%              Depth                    :   21
%              Number of atoms          :  557 (41013 expanded)
%              Number of equality atoms :   22 (2604 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   67 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t43_waybel_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_waybel_0(X2,X1)
          <=> ! [X3] :
                ( ( v1_finset_1(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X2)) )
               => ( X3 != k1_xboole_0
                 => r2_hidden(k2_yellow_0(X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',t43_waybel_0)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',cc2_lattice3)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',t3_subset)).

fof(t2_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,X1) )
          <=> ! [X3] :
                ( ( v1_finset_1(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X2)) )
               => ? [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                    & r2_hidden(X4,X2)
                    & r1_lattice3(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',t2_waybel_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',t1_xboole_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',t4_subset)).

fof(t55_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v2_lattice3(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_finset_1(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => r2_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',t55_yellow_0)).

fof(t31_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) )
               => ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) ) )
              & ( ( r1_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X4,X2) ) ) )
               => ( X2 = k2_yellow_0(X1,X3)
                  & r2_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',t31_yellow_0)).

fof(dt_k2_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',dt_k2_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',existence_m1_subset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',t6_boole)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',t6_yellow_0)).

fof(d20_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v13_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X3,X4) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/waybel_0__t43_waybel_0.p',d20_waybel_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v2_waybel_0(X2,X1)
            <=> ! [X3] :
                  ( ( v1_finset_1(X3)
                    & m1_subset_1(X3,k1_zfmisc_1(X2)) )
                 => ( X3 != k1_xboole_0
                   => r2_hidden(k2_yellow_0(X1,X3),X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t43_waybel_0])).

fof(c_0_15,plain,(
    ! [X13] :
      ( ~ l1_orders_2(X13)
      | ~ v2_lattice3(X13)
      | ~ v2_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_16,negated_conjecture,(
    ! [X8] :
      ( v3_orders_2(esk1_0)
      & v4_orders_2(esk1_0)
      & v5_orders_2(esk1_0)
      & v2_lattice3(esk1_0)
      & l1_orders_2(esk1_0)
      & ~ v1_xboole_0(esk2_0)
      & v13_waybel_0(esk2_0,esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( v1_finset_1(esk3_0)
        | ~ v2_waybel_0(esk2_0,esk1_0) )
      & ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
        | ~ v2_waybel_0(esk2_0,esk1_0) )
      & ( esk3_0 != k1_xboole_0
        | ~ v2_waybel_0(esk2_0,esk1_0) )
      & ( ~ r2_hidden(k2_yellow_0(esk1_0,esk3_0),esk2_0)
        | ~ v2_waybel_0(esk2_0,esk1_0) )
      & ( v2_waybel_0(esk2_0,esk1_0)
        | ~ v1_finset_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(esk2_0))
        | X8 = k1_xboole_0
        | r2_hidden(k2_yellow_0(esk1_0,X8),esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).

fof(c_0_17,plain,(
    ! [X63,X64] :
      ( ( ~ m1_subset_1(X63,k1_zfmisc_1(X64))
        | r1_tarski(X63,X64) )
      & ( ~ r1_tarski(X63,X64)
        | m1_subset_1(X63,k1_zfmisc_1(X64)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,plain,(
    ! [X51,X52,X53,X56] :
      ( ( m1_subset_1(esk13_3(X51,X52,X53),u1_struct_0(X51))
        | ~ v1_finset_1(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X52))
        | v1_xboole_0(X52)
        | ~ v2_waybel_0(X52,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | v2_struct_0(X51)
        | ~ v4_orders_2(X51)
        | ~ l1_orders_2(X51) )
      & ( r2_hidden(esk13_3(X51,X52,X53),X52)
        | ~ v1_finset_1(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X52))
        | v1_xboole_0(X52)
        | ~ v2_waybel_0(X52,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | v2_struct_0(X51)
        | ~ v4_orders_2(X51)
        | ~ l1_orders_2(X51) )
      & ( r1_lattice3(X51,X53,esk13_3(X51,X52,X53))
        | ~ v1_finset_1(X53)
        | ~ m1_subset_1(X53,k1_zfmisc_1(X52))
        | v1_xboole_0(X52)
        | ~ v2_waybel_0(X52,X51)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | v2_struct_0(X51)
        | ~ v4_orders_2(X51)
        | ~ l1_orders_2(X51) )
      & ( ~ v1_xboole_0(X52)
        | v1_finset_1(esk14_2(X51,X52))
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | v2_struct_0(X51)
        | ~ v4_orders_2(X51)
        | ~ l1_orders_2(X51) )
      & ( v2_waybel_0(X52,X51)
        | v1_finset_1(esk14_2(X51,X52))
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | v2_struct_0(X51)
        | ~ v4_orders_2(X51)
        | ~ l1_orders_2(X51) )
      & ( ~ v1_xboole_0(X52)
        | m1_subset_1(esk14_2(X51,X52),k1_zfmisc_1(X52))
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | v2_struct_0(X51)
        | ~ v4_orders_2(X51)
        | ~ l1_orders_2(X51) )
      & ( v2_waybel_0(X52,X51)
        | m1_subset_1(esk14_2(X51,X52),k1_zfmisc_1(X52))
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | v2_struct_0(X51)
        | ~ v4_orders_2(X51)
        | ~ l1_orders_2(X51) )
      & ( ~ v1_xboole_0(X52)
        | ~ m1_subset_1(X56,u1_struct_0(X51))
        | ~ r2_hidden(X56,X52)
        | ~ r1_lattice3(X51,esk14_2(X51,X52),X56)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | v2_struct_0(X51)
        | ~ v4_orders_2(X51)
        | ~ l1_orders_2(X51) )
      & ( v2_waybel_0(X52,X51)
        | ~ m1_subset_1(X56,u1_struct_0(X51))
        | ~ r2_hidden(X56,X52)
        | ~ r1_lattice3(X51,esk14_2(X51,X52),X56)
        | ~ m1_subset_1(X52,k1_zfmisc_1(u1_struct_0(X51)))
        | v2_struct_0(X51)
        | ~ v4_orders_2(X51)
        | ~ l1_orders_2(X51) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t2_waybel_0])])])])])])).

cnf(c_0_19,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X46,X47,X48] :
      ( ~ r1_tarski(X46,X47)
      | ~ r1_tarski(X47,X48)
      | r1_tarski(X46,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v2_waybel_0(X1,X2)
    | m1_subset_1(esk14_2(X2,X1),k1_zfmisc_1(X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_26,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X3)
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_29,negated_conjecture,
    ( r1_tarski(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | m1_subset_1(esk14_2(esk1_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_21]),c_0_26])]),c_0_27])).

fof(c_0_31,plain,(
    ! [X65,X66,X67] :
      ( ~ r2_hidden(X65,X66)
      | ~ m1_subset_1(X66,k1_zfmisc_1(X67))
      | m1_subset_1(X65,X67) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_32,plain,(
    ! [X68,X69] :
      ( ( ~ v2_lattice3(X68)
        | v1_xboole_0(X69)
        | ~ v1_finset_1(X69)
        | ~ m1_subset_1(X69,k1_zfmisc_1(u1_struct_0(X68)))
        | r2_yellow_0(X68,X69)
        | v2_struct_0(X68)
        | ~ v3_orders_2(X68)
        | ~ v4_orders_2(X68)
        | ~ v5_orders_2(X68)
        | ~ l1_orders_2(X68) )
      & ( ~ v1_xboole_0(esk16_1(X68))
        | v2_lattice3(X68)
        | v2_struct_0(X68)
        | ~ v3_orders_2(X68)
        | ~ v4_orders_2(X68)
        | ~ v5_orders_2(X68)
        | ~ l1_orders_2(X68) )
      & ( v1_finset_1(esk16_1(X68))
        | v2_lattice3(X68)
        | v2_struct_0(X68)
        | ~ v3_orders_2(X68)
        | ~ v4_orders_2(X68)
        | ~ v5_orders_2(X68)
        | ~ l1_orders_2(X68) )
      & ( m1_subset_1(esk16_1(X68),k1_zfmisc_1(u1_struct_0(X68)))
        | v2_lattice3(X68)
        | v2_struct_0(X68)
        | ~ v3_orders_2(X68)
        | ~ v4_orders_2(X68)
        | ~ v5_orders_2(X68)
        | ~ l1_orders_2(X68) )
      & ( ~ r2_yellow_0(X68,esk16_1(X68))
        | v2_lattice3(X68)
        | v2_struct_0(X68)
        | ~ v3_orders_2(X68)
        | ~ v4_orders_2(X68)
        | ~ v5_orders_2(X68)
        | ~ l1_orders_2(X68) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_yellow_0])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk14_2(esk1_0,esk2_0),esk2_0)
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_35,plain,
    ( v2_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_lattice3(X2,esk14_2(X2,X1),X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_36,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_37,plain,
    ( v2_waybel_0(X1,X2)
    | v1_finset_1(esk14_2(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_38,plain,(
    ! [X57,X58,X59,X60,X61] :
      ( ( r1_lattice3(X57,X59,X58)
        | X58 != k2_yellow_0(X57,X59)
        | ~ r2_yellow_0(X57,X59)
        | ~ m1_subset_1(X58,u1_struct_0(X57))
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) )
      & ( ~ m1_subset_1(X60,u1_struct_0(X57))
        | ~ r1_lattice3(X57,X59,X60)
        | r1_orders_2(X57,X60,X58)
        | X58 != k2_yellow_0(X57,X59)
        | ~ r2_yellow_0(X57,X59)
        | ~ m1_subset_1(X58,u1_struct_0(X57))
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) )
      & ( X58 = k2_yellow_0(X57,X61)
        | m1_subset_1(esk15_3(X57,X58,X61),u1_struct_0(X57))
        | ~ r1_lattice3(X57,X61,X58)
        | ~ m1_subset_1(X58,u1_struct_0(X57))
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) )
      & ( r2_yellow_0(X57,X61)
        | m1_subset_1(esk15_3(X57,X58,X61),u1_struct_0(X57))
        | ~ r1_lattice3(X57,X61,X58)
        | ~ m1_subset_1(X58,u1_struct_0(X57))
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) )
      & ( X58 = k2_yellow_0(X57,X61)
        | r1_lattice3(X57,X61,esk15_3(X57,X58,X61))
        | ~ r1_lattice3(X57,X61,X58)
        | ~ m1_subset_1(X58,u1_struct_0(X57))
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) )
      & ( r2_yellow_0(X57,X61)
        | r1_lattice3(X57,X61,esk15_3(X57,X58,X61))
        | ~ r1_lattice3(X57,X61,X58)
        | ~ m1_subset_1(X58,u1_struct_0(X57))
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) )
      & ( X58 = k2_yellow_0(X57,X61)
        | ~ r1_orders_2(X57,esk15_3(X57,X58,X61),X58)
        | ~ r1_lattice3(X57,X61,X58)
        | ~ m1_subset_1(X58,u1_struct_0(X57))
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) )
      & ( r2_yellow_0(X57,X61)
        | ~ r1_orders_2(X57,esk15_3(X57,X58,X61),X58)
        | ~ r1_lattice3(X57,X61,X58)
        | ~ m1_subset_1(X58,u1_struct_0(X57))
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t31_yellow_0])])])])])])).

fof(c_0_39,plain,(
    ! [X20,X21] :
      ( ~ l1_orders_2(X20)
      | m1_subset_1(k2_yellow_0(X20,X21),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k2_yellow_0])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X2)
    | r2_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v2_lattice3(X1)
    | ~ v1_finset_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_32])).

cnf(c_0_41,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_42,negated_conjecture,
    ( r1_tarski(esk14_2(esk1_0,esk2_0),u1_struct_0(esk1_0))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_43,plain,(
    ! [X49,X50] :
      ( ~ m1_subset_1(X49,X50)
      | v1_xboole_0(X50)
      | r2_hidden(X49,X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_44,plain,(
    ! [X30] : m1_subset_1(esk8_1(X30),X30) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | v2_waybel_0(X2,X1)
    | ~ r1_lattice3(X1,esk14_2(X1,X2),X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | X1 = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk1_0,X1),esk2_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( v1_finset_1(esk14_2(esk1_0,esk2_0))
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_24]),c_0_21]),c_0_26])]),c_0_27])).

cnf(c_0_48,plain,
    ( r1_lattice3(X1,X2,X3)
    | X3 != k2_yellow_0(X1,X2)
    | ~ r2_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( m1_subset_1(k2_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( r2_yellow_0(X1,X2)
    | v1_xboole_0(X2)
    | ~ v1_finset_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_40,c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | m1_subset_1(esk14_2(esk1_0,esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_52,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_53,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_54,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_55,plain,
    ( m1_subset_1(esk8_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_44])).

cnf(c_0_56,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | ~ r1_lattice3(esk1_0,esk14_2(esk1_0,esk2_0),X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_21]),c_0_26])]),c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( esk14_2(esk1_0,esk2_0) = k1_xboole_0
    | r2_hidden(k2_yellow_0(esk1_0,esk14_2(esk1_0,esk2_0)),esk2_0)
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_30]),c_0_47])).

cnf(c_0_58,plain,
    ( r1_lattice3(X1,X2,k2_yellow_0(X1,X2))
    | ~ r2_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk14_2(esk1_0,esk2_0))
    | v2_waybel_0(esk2_0,esk1_0)
    | v1_xboole_0(esk14_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_21]),c_0_20]),c_0_52]),c_0_26]),c_0_53])]),c_0_47])).

fof(c_0_60,plain,(
    ! [X74] :
      ( ~ v1_xboole_0(X74)
      | X74 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_61,plain,(
    ! [X75,X76] :
      ( ( r2_lattice3(X75,k1_xboole_0,X76)
        | ~ m1_subset_1(X76,u1_struct_0(X75))
        | ~ l1_orders_2(X75) )
      & ( r1_lattice3(X75,k1_xboole_0,X76)
        | ~ m1_subset_1(X76,u1_struct_0(X75))
        | ~ l1_orders_2(X75) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_yellow_0])])])])).

cnf(c_0_62,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_36,c_0_24])).

cnf(c_0_63,plain,
    ( r2_hidden(esk8_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_64,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_65,negated_conjecture,
    ( esk14_2(esk1_0,esk2_0) = k1_xboole_0
    | v2_waybel_0(esk2_0,esk1_0)
    | ~ r1_lattice3(esk1_0,esk14_2(esk1_0,esk2_0),k2_yellow_0(esk1_0,esk14_2(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r1_lattice3(esk1_0,esk14_2(esk1_0,esk2_0),k2_yellow_0(esk1_0,esk14_2(esk1_0,esk2_0)))
    | v2_waybel_0(esk2_0,esk1_0)
    | v1_xboole_0(esk14_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_21]),c_0_52])])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( r1_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk8_1(esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0)
    | ~ r1_lattice3(esk1_0,esk14_2(esk1_0,esk2_0),esk8_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_63]),c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( esk14_2(esk1_0,esk2_0) = k1_xboole_0
    | v2_waybel_0(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( r1_lattice3(esk1_0,k1_xboole_0,esk8_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_21])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_74,negated_conjecture,
    ( v2_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( v1_finset_1(esk3_0)
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_76,plain,
    ( r2_hidden(esk13_3(X1,X2,X3),X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v1_finset_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_77,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_73,c_0_74])])).

cnf(c_0_78,negated_conjecture,
    ( v1_finset_1(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_75,c_0_74])])).

fof(c_0_79,plain,(
    ! [X14,X15,X16,X17] :
      ( ( ~ v13_waybel_0(X15,X14)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X16,X15)
        | ~ r1_orders_2(X14,X16,X17)
        | r2_hidden(X17,X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk4_2(X14,X15),u1_struct_0(X14))
        | v13_waybel_0(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk5_2(X14,X15),u1_struct_0(X14))
        | v13_waybel_0(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk4_2(X14,X15),X15)
        | v13_waybel_0(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) )
      & ( r1_orders_2(X14,esk4_2(X14,X15),esk5_2(X14,X15))
        | v13_waybel_0(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) )
      & ( ~ r2_hidden(esk5_2(X14,X15),X15)
        | v13_waybel_0(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

cnf(c_0_80,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk13_3(X1,esk2_0,esk3_0),esk2_0)
    | ~ v2_waybel_0(esk2_0,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),c_0_64])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_77])).

cnf(c_0_82,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_83,plain,
    ( r1_orders_2(X2,X1,X4)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r1_lattice3(X2,X3,X1)
    | X4 != k2_yellow_0(X2,X3)
    | ~ r2_yellow_0(X2,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(esk13_3(esk1_0,esk2_0,esk3_0),esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_74]),c_0_24]),c_0_21]),c_0_26])]),c_0_27])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(esk3_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_33,c_0_81])).

cnf(c_0_86,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v13_waybel_0(X2,X3)
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_82,c_0_36])).

cnf(c_0_87,plain,
    ( r1_orders_2(X1,X2,k2_yellow_0(X1,X3))
    | ~ r2_yellow_0(X1,X3)
    | ~ r1_lattice3(X1,X3,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_83]),c_0_49])).

cnf(c_0_88,negated_conjecture,
    ( m1_subset_1(esk13_3(esk1_0,esk2_0,esk3_0),u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_84])).

cnf(c_0_89,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(spm,[status(thm)],[c_0_41,c_0_85])).

cnf(c_0_90,plain,
    ( r1_lattice3(X1,X2,esk13_3(X1,X3,X2))
    | v1_xboole_0(X3)
    | v2_struct_0(X1)
    | ~ v1_finset_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v2_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_91,plain,
    ( r2_hidden(k2_yellow_0(X1,X2),X3)
    | ~ r1_orders_2(X1,X4,k2_yellow_0(X1,X2))
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v13_waybel_0(X3,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_49])).

cnf(c_0_92,negated_conjecture,
    ( v13_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_93,negated_conjecture,
    ( r1_orders_2(esk1_0,esk13_3(esk1_0,esk2_0,esk3_0),k2_yellow_0(esk1_0,X1))
    | ~ r2_yellow_0(esk1_0,X1)
    | ~ r1_lattice3(esk1_0,X1,esk13_3(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_21]),c_0_52])])).

cnf(c_0_94,negated_conjecture,
    ( r2_yellow_0(esk1_0,esk3_0)
    | v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_89]),c_0_78]),c_0_21]),c_0_20]),c_0_52]),c_0_26]),c_0_53])])).

cnf(c_0_95,negated_conjecture,
    ( r1_lattice3(X1,esk3_0,esk13_3(X1,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v2_waybel_0(esk2_0,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_77]),c_0_78])]),c_0_64])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(k2_yellow_0(esk1_0,X1),esk2_0)
    | ~ r1_orders_2(esk1_0,X2,k2_yellow_0(esk1_0,X1))
    | ~ r2_hidden(X2,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_24]),c_0_92]),c_0_21])])).

cnf(c_0_97,negated_conjecture,
    ( r1_orders_2(esk1_0,esk13_3(esk1_0,esk2_0,esk3_0),k2_yellow_0(esk1_0,esk3_0))
    | v1_xboole_0(esk3_0)
    | ~ r1_lattice3(esk1_0,esk3_0,esk13_3(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r1_lattice3(esk1_0,esk3_0,esk13_3(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_74]),c_0_24]),c_0_21]),c_0_26])]),c_0_27])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(k2_yellow_0(esk1_0,esk3_0),esk2_0)
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(k2_yellow_0(esk1_0,X1),esk2_0)
    | ~ r1_orders_2(esk1_0,esk13_3(esk1_0,esk2_0,esk3_0),k2_yellow_0(esk1_0,X1)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_84])).

cnf(c_0_101,negated_conjecture,
    ( r1_orders_2(esk1_0,esk13_3(esk1_0,esk2_0,esk3_0),k2_yellow_0(esk1_0,esk3_0))
    | v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98])])).

cnf(c_0_102,negated_conjecture,
    ( ~ r2_hidden(k2_yellow_0(esk1_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_74])])).

cnf(c_0_103,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v2_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_104,negated_conjecture,
    ( v1_xboole_0(esk3_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])).

cnf(c_0_105,negated_conjecture,
    ( esk3_0 != k1_xboole_0 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_103,c_0_74])])).

cnf(c_0_106,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_104]),c_0_105]),
    [proof]).
%------------------------------------------------------------------------------
