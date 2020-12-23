%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t42_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:50 EDT 2019

% Result     : Theorem 178.61s
% Output     : CNFRefutation 178.61s
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
fof(t42_waybel_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_waybel_0(X2,X1)
          <=> ! [X3] :
                ( ( v1_finset_1(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X2)) )
               => ( X3 != k1_xboole_0
                 => r2_hidden(k1_yellow_0(X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t42_waybel_0)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',cc1_lattice3)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t3_subset)).

fof(t1_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1) )
          <=> ! [X3] :
                ( ( v1_finset_1(X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X2)) )
               => ? [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                    & r2_hidden(X4,X2)
                    & r2_lattice3(X1,X3,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t1_waybel_0)).

fof(t1_xboole_1,axiom,(
    ! [X1,X2,X3] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X2,X3) )
     => r1_tarski(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t1_xboole_1)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t4_subset)).

fof(t54_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_lattice3(X1)
      <=> ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_finset_1(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => r1_yellow_0(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t54_yellow_0)).

fof(t30_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( ( ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) )
               => ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) ) )
              & ( ( r2_lattice3(X1,X3,X2)
                  & ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r2_lattice3(X1,X3,X4)
                       => r1_orders_2(X1,X2,X4) ) ) )
               => ( X2 = k1_yellow_0(X1,X3)
                  & r1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t30_yellow_0)).

fof(dt_k1_yellow_0,axiom,(
    ! [X1,X2] :
      ( l1_orders_2(X1)
     => m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',dt_k1_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',existence_m1_subset_1)).

fof(t6_boole,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
     => X1 = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t6_boole)).

fof(t6_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r2_lattice3(X1,k1_xboole_0,X2)
            & r1_lattice3(X1,k1_xboole_0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',t6_yellow_0)).

fof(d19_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v12_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,X2)
                        & r1_orders_2(X1,X4,X3) )
                     => r2_hidden(X4,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t42_waybel_0.p',d19_waybel_0)).

fof(c_0_14,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v12_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v1_waybel_0(X2,X1)
            <=> ! [X3] :
                  ( ( v1_finset_1(X3)
                    & m1_subset_1(X3,k1_zfmisc_1(X2)) )
                 => ( X3 != k1_xboole_0
                   => r2_hidden(k1_yellow_0(X1,X3),X2) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t42_waybel_0])).

fof(c_0_15,plain,(
    ! [X12] :
      ( ~ l1_orders_2(X12)
      | ~ v1_lattice3(X12)
      | ~ v2_struct_0(X12) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_16,negated_conjecture,(
    ! [X8] :
      ( v3_orders_2(esk1_0)
      & v4_orders_2(esk1_0)
      & v5_orders_2(esk1_0)
      & v1_lattice3(esk1_0)
      & l1_orders_2(esk1_0)
      & ~ v1_xboole_0(esk2_0)
      & v12_waybel_0(esk2_0,esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & ( v1_finset_1(esk3_0)
        | ~ v1_waybel_0(esk2_0,esk1_0) )
      & ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
        | ~ v1_waybel_0(esk2_0,esk1_0) )
      & ( esk3_0 != k1_xboole_0
        | ~ v1_waybel_0(esk2_0,esk1_0) )
      & ( ~ r2_hidden(k1_yellow_0(esk1_0,esk3_0),esk2_0)
        | ~ v1_waybel_0(esk2_0,esk1_0) )
      & ( v1_waybel_0(esk2_0,esk1_0)
        | ~ v1_finset_1(X8)
        | ~ m1_subset_1(X8,k1_zfmisc_1(esk2_0))
        | X8 = k1_xboole_0
        | r2_hidden(k1_yellow_0(esk1_0,X8),esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_14])])])])])])).

fof(c_0_17,plain,(
    ! [X69,X70] :
      ( ( ~ m1_subset_1(X69,k1_zfmisc_1(X70))
        | r1_tarski(X69,X70) )
      & ( ~ r1_tarski(X69,X70)
        | m1_subset_1(X69,k1_zfmisc_1(X70)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_18,plain,(
    ! [X52,X53,X54,X57] :
      ( ( m1_subset_1(esk13_3(X52,X53,X54),u1_struct_0(X52))
        | ~ v1_finset_1(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X53))
        | v1_xboole_0(X53)
        | ~ v1_waybel_0(X53,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ l1_orders_2(X52) )
      & ( r2_hidden(esk13_3(X52,X53,X54),X53)
        | ~ v1_finset_1(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X53))
        | v1_xboole_0(X53)
        | ~ v1_waybel_0(X53,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ l1_orders_2(X52) )
      & ( r2_lattice3(X52,X54,esk13_3(X52,X53,X54))
        | ~ v1_finset_1(X54)
        | ~ m1_subset_1(X54,k1_zfmisc_1(X53))
        | v1_xboole_0(X53)
        | ~ v1_waybel_0(X53,X52)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ l1_orders_2(X52) )
      & ( ~ v1_xboole_0(X53)
        | v1_finset_1(esk14_2(X52,X53))
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ l1_orders_2(X52) )
      & ( v1_waybel_0(X53,X52)
        | v1_finset_1(esk14_2(X52,X53))
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ l1_orders_2(X52) )
      & ( ~ v1_xboole_0(X53)
        | m1_subset_1(esk14_2(X52,X53),k1_zfmisc_1(X53))
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ l1_orders_2(X52) )
      & ( v1_waybel_0(X53,X52)
        | m1_subset_1(esk14_2(X52,X53),k1_zfmisc_1(X53))
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ l1_orders_2(X52) )
      & ( ~ v1_xboole_0(X53)
        | ~ m1_subset_1(X57,u1_struct_0(X52))
        | ~ r2_hidden(X57,X53)
        | ~ r2_lattice3(X52,esk14_2(X52,X53),X57)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ l1_orders_2(X52) )
      & ( v1_waybel_0(X53,X52)
        | ~ m1_subset_1(X57,u1_struct_0(X52))
        | ~ r2_hidden(X57,X53)
        | ~ r2_lattice3(X52,esk14_2(X52,X53),X57)
        | ~ m1_subset_1(X53,k1_zfmisc_1(u1_struct_0(X52)))
        | v2_struct_0(X52)
        | ~ v4_orders_2(X52)
        | ~ l1_orders_2(X52) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t1_waybel_0])])])])])])).

cnf(c_0_19,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_20,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

fof(c_0_22,plain,(
    ! [X58,X59,X60] :
      ( ~ r1_tarski(X58,X59)
      | ~ r1_tarski(X59,X60)
      | r1_tarski(X58,X60) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_xboole_1])])).

cnf(c_0_23,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_25,plain,
    ( v1_waybel_0(X1,X2)
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
    ( v1_waybel_0(esk2_0,esk1_0)
    | m1_subset_1(esk14_2(esk1_0,esk2_0),k1_zfmisc_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_21]),c_0_26])]),c_0_27])).

fof(c_0_31,plain,(
    ! [X71,X72,X73] :
      ( ~ r2_hidden(X71,X72)
      | ~ m1_subset_1(X72,k1_zfmisc_1(X73))
      | m1_subset_1(X71,X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_32,plain,(
    ! [X74,X75] :
      ( ( ~ v1_lattice3(X74)
        | v1_xboole_0(X75)
        | ~ v1_finset_1(X75)
        | ~ m1_subset_1(X75,k1_zfmisc_1(u1_struct_0(X74)))
        | r1_yellow_0(X74,X75)
        | v2_struct_0(X74)
        | ~ v3_orders_2(X74)
        | ~ v4_orders_2(X74)
        | ~ v5_orders_2(X74)
        | ~ l1_orders_2(X74) )
      & ( ~ v1_xboole_0(esk16_1(X74))
        | v1_lattice3(X74)
        | v2_struct_0(X74)
        | ~ v3_orders_2(X74)
        | ~ v4_orders_2(X74)
        | ~ v5_orders_2(X74)
        | ~ l1_orders_2(X74) )
      & ( v1_finset_1(esk16_1(X74))
        | v1_lattice3(X74)
        | v2_struct_0(X74)
        | ~ v3_orders_2(X74)
        | ~ v4_orders_2(X74)
        | ~ v5_orders_2(X74)
        | ~ l1_orders_2(X74) )
      & ( m1_subset_1(esk16_1(X74),k1_zfmisc_1(u1_struct_0(X74)))
        | v1_lattice3(X74)
        | v2_struct_0(X74)
        | ~ v3_orders_2(X74)
        | ~ v4_orders_2(X74)
        | ~ v5_orders_2(X74)
        | ~ l1_orders_2(X74) )
      & ( ~ r1_yellow_0(X74,esk16_1(X74))
        | v1_lattice3(X74)
        | v2_struct_0(X74)
        | ~ v3_orders_2(X74)
        | ~ v4_orders_2(X74)
        | ~ v5_orders_2(X74)
        | ~ l1_orders_2(X74) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t54_yellow_0])])])])])])).

cnf(c_0_33,negated_conjecture,
    ( r1_tarski(X1,u1_struct_0(esk1_0))
    | ~ r1_tarski(X1,esk2_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

cnf(c_0_34,negated_conjecture,
    ( r1_tarski(esk14_2(esk1_0,esk2_0),esk2_0)
    | v1_waybel_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_30])).

cnf(c_0_35,plain,
    ( v1_waybel_0(X1,X2)
    | v2_struct_0(X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r2_lattice3(X2,esk14_2(X2,X1),X3)
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
    ( v1_waybel_0(X1,X2)
    | v1_finset_1(esk14_2(X2,X1))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_38,plain,(
    ! [X63,X64,X65,X66,X67] :
      ( ( r2_lattice3(X63,X65,X64)
        | X64 != k1_yellow_0(X63,X65)
        | ~ r1_yellow_0(X63,X65)
        | ~ m1_subset_1(X64,u1_struct_0(X63))
        | ~ v5_orders_2(X63)
        | ~ l1_orders_2(X63) )
      & ( ~ m1_subset_1(X66,u1_struct_0(X63))
        | ~ r2_lattice3(X63,X65,X66)
        | r1_orders_2(X63,X64,X66)
        | X64 != k1_yellow_0(X63,X65)
        | ~ r1_yellow_0(X63,X65)
        | ~ m1_subset_1(X64,u1_struct_0(X63))
        | ~ v5_orders_2(X63)
        | ~ l1_orders_2(X63) )
      & ( X64 = k1_yellow_0(X63,X67)
        | m1_subset_1(esk15_3(X63,X64,X67),u1_struct_0(X63))
        | ~ r2_lattice3(X63,X67,X64)
        | ~ m1_subset_1(X64,u1_struct_0(X63))
        | ~ v5_orders_2(X63)
        | ~ l1_orders_2(X63) )
      & ( r1_yellow_0(X63,X67)
        | m1_subset_1(esk15_3(X63,X64,X67),u1_struct_0(X63))
        | ~ r2_lattice3(X63,X67,X64)
        | ~ m1_subset_1(X64,u1_struct_0(X63))
        | ~ v5_orders_2(X63)
        | ~ l1_orders_2(X63) )
      & ( X64 = k1_yellow_0(X63,X67)
        | r2_lattice3(X63,X67,esk15_3(X63,X64,X67))
        | ~ r2_lattice3(X63,X67,X64)
        | ~ m1_subset_1(X64,u1_struct_0(X63))
        | ~ v5_orders_2(X63)
        | ~ l1_orders_2(X63) )
      & ( r1_yellow_0(X63,X67)
        | r2_lattice3(X63,X67,esk15_3(X63,X64,X67))
        | ~ r2_lattice3(X63,X67,X64)
        | ~ m1_subset_1(X64,u1_struct_0(X63))
        | ~ v5_orders_2(X63)
        | ~ l1_orders_2(X63) )
      & ( X64 = k1_yellow_0(X63,X67)
        | ~ r1_orders_2(X63,X64,esk15_3(X63,X64,X67))
        | ~ r2_lattice3(X63,X67,X64)
        | ~ m1_subset_1(X64,u1_struct_0(X63))
        | ~ v5_orders_2(X63)
        | ~ l1_orders_2(X63) )
      & ( r1_yellow_0(X63,X67)
        | ~ r1_orders_2(X63,X64,esk15_3(X63,X64,X67))
        | ~ r2_lattice3(X63,X67,X64)
        | ~ m1_subset_1(X64,u1_struct_0(X63))
        | ~ v5_orders_2(X63)
        | ~ l1_orders_2(X63) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[t30_yellow_0])])])])])])).

fof(c_0_39,plain,(
    ! [X20,X21] :
      ( ~ l1_orders_2(X20)
      | m1_subset_1(k1_yellow_0(X20,X21),u1_struct_0(X20)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_yellow_0])])).

cnf(c_0_40,plain,
    ( v1_xboole_0(X2)
    | r1_yellow_0(X1,X2)
    | v2_struct_0(X1)
    | ~ v1_lattice3(X1)
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
    | v1_waybel_0(esk2_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_33,c_0_34])).

fof(c_0_43,plain,(
    ! [X61,X62] :
      ( ~ m1_subset_1(X61,X62)
      | v1_xboole_0(X62)
      | r2_hidden(X61,X62) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_44,plain,(
    ! [X30] : m1_subset_1(esk8_1(X30),X30) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_45,plain,
    ( v2_struct_0(X1)
    | v1_waybel_0(X2,X1)
    | ~ r2_lattice3(X1,esk14_2(X1,X2),X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_46,negated_conjecture,
    ( v1_waybel_0(esk2_0,esk1_0)
    | X1 = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk1_0,X1),esk2_0)
    | ~ v1_finset_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_47,negated_conjecture,
    ( v1_finset_1(esk14_2(esk1_0,esk2_0))
    | v1_waybel_0(esk2_0,esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_24]),c_0_21]),c_0_26])]),c_0_27])).

cnf(c_0_48,plain,
    ( r2_lattice3(X1,X2,X3)
    | X3 != k1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_38])).

cnf(c_0_49,plain,
    ( m1_subset_1(k1_yellow_0(X1,X2),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,plain,
    ( r1_yellow_0(X1,X2)
    | v1_xboole_0(X2)
    | ~ v1_finset_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[c_0_40,c_0_19])).

cnf(c_0_51,negated_conjecture,
    ( v1_waybel_0(esk2_0,esk1_0)
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
    ( v1_waybel_0(esk2_0,esk1_0)
    | ~ r2_lattice3(esk1_0,esk14_2(esk1_0,esk2_0),X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_24]),c_0_21]),c_0_26])]),c_0_27])).

cnf(c_0_57,negated_conjecture,
    ( esk14_2(esk1_0,esk2_0) = k1_xboole_0
    | r2_hidden(k1_yellow_0(esk1_0,esk14_2(esk1_0,esk2_0)),esk2_0)
    | v1_waybel_0(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_30]),c_0_47])).

cnf(c_0_58,plain,
    ( r2_lattice3(X1,X2,k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_48]),c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk14_2(esk1_0,esk2_0))
    | v1_waybel_0(esk2_0,esk1_0)
    | v1_xboole_0(esk14_2(esk1_0,esk2_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_21]),c_0_20]),c_0_52]),c_0_26]),c_0_53])]),c_0_47])).

fof(c_0_60,plain,(
    ! [X80] :
      ( ~ v1_xboole_0(X80)
      | X80 = k1_xboole_0 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t6_boole])])).

fof(c_0_61,plain,(
    ! [X81,X82] :
      ( ( r2_lattice3(X81,k1_xboole_0,X82)
        | ~ m1_subset_1(X82,u1_struct_0(X81))
        | ~ l1_orders_2(X81) )
      & ( r1_lattice3(X81,k1_xboole_0,X82)
        | ~ m1_subset_1(X82,u1_struct_0(X81))
        | ~ l1_orders_2(X81) ) ) ),
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
    | v1_waybel_0(esk2_0,esk1_0)
    | ~ r2_lattice3(esk1_0,esk14_2(esk1_0,esk2_0),k1_yellow_0(esk1_0,esk14_2(esk1_0,esk2_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r2_lattice3(esk1_0,esk14_2(esk1_0,esk2_0),k1_yellow_0(esk1_0,esk14_2(esk1_0,esk2_0)))
    | v1_waybel_0(esk2_0,esk1_0)
    | v1_xboole_0(esk14_2(esk1_0,esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_21]),c_0_52])])).

cnf(c_0_67,plain,
    ( X1 = k1_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_68,plain,
    ( r2_lattice3(X1,k1_xboole_0,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( m1_subset_1(esk8_1(esk2_0),u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_63]),c_0_64])).

cnf(c_0_70,negated_conjecture,
    ( v1_waybel_0(esk2_0,esk1_0)
    | ~ r2_lattice3(esk1_0,esk14_2(esk1_0,esk2_0),esk8_1(esk2_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_63]),c_0_64])).

cnf(c_0_71,negated_conjecture,
    ( esk14_2(esk1_0,esk2_0) = k1_xboole_0
    | v1_waybel_0(esk2_0,esk1_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_67])).

cnf(c_0_72,negated_conjecture,
    ( r2_lattice3(esk1_0,k1_xboole_0,esk8_1(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_69]),c_0_21])])).

cnf(c_0_73,negated_conjecture,
    ( m1_subset_1(esk3_0,k1_zfmisc_1(esk2_0))
    | ~ v1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_74,negated_conjecture,
    ( v1_waybel_0(esk2_0,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_75,negated_conjecture,
    ( v1_finset_1(esk3_0)
    | ~ v1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_76,plain,
    ( r2_hidden(esk13_3(X1,X2,X3),X2)
    | v1_xboole_0(X2)
    | v2_struct_0(X1)
    | ~ v1_finset_1(X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ v1_waybel_0(X2,X1)
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
      ( ( ~ v12_waybel_0(X15,X14)
        | ~ m1_subset_1(X16,u1_struct_0(X14))
        | ~ m1_subset_1(X17,u1_struct_0(X14))
        | ~ r2_hidden(X16,X15)
        | ~ r1_orders_2(X14,X17,X16)
        | r2_hidden(X17,X15)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk4_2(X14,X15),u1_struct_0(X14))
        | v12_waybel_0(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) )
      & ( m1_subset_1(esk5_2(X14,X15),u1_struct_0(X14))
        | v12_waybel_0(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) )
      & ( r2_hidden(esk4_2(X14,X15),X15)
        | v12_waybel_0(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) )
      & ( r1_orders_2(X14,esk5_2(X14,X15),esk4_2(X14,X15))
        | v12_waybel_0(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) )
      & ( ~ r2_hidden(esk5_2(X14,X15),X15)
        | v12_waybel_0(X15,X14)
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ l1_orders_2(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_waybel_0])])])])])).

cnf(c_0_80,negated_conjecture,
    ( v2_struct_0(X1)
    | r2_hidden(esk13_3(X1,esk2_0,esk3_0),esk2_0)
    | ~ v1_waybel_0(esk2_0,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_78])]),c_0_64])).

cnf(c_0_81,negated_conjecture,
    ( r1_tarski(esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_23,c_0_77])).

cnf(c_0_82,plain,
    ( r2_hidden(X4,X1)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_83,plain,
    ( r1_orders_2(X2,X4,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_lattice3(X2,X3,X1)
    | X4 != k1_yellow_0(X2,X3)
    | ~ r1_yellow_0(X2,X3)
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
    | ~ r1_orders_2(X3,X1,X4)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v12_waybel_0(X2,X3)
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_82,c_0_36])).

cnf(c_0_87,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r2_lattice3(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
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
    ( r2_lattice3(X1,X2,esk13_3(X1,X3,X2))
    | v1_xboole_0(X3)
    | v2_struct_0(X1)
    | ~ v1_finset_1(X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_91,plain,
    ( r2_hidden(k1_yellow_0(X1,X2),X3)
    | ~ r1_orders_2(X1,k1_yellow_0(X1,X2),X4)
    | ~ r2_hidden(X4,X3)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v12_waybel_0(X3,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_86,c_0_49])).

cnf(c_0_92,negated_conjecture,
    ( v12_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_93,negated_conjecture,
    ( r1_orders_2(esk1_0,k1_yellow_0(esk1_0,X1),esk13_3(esk1_0,esk2_0,esk3_0))
    | ~ r1_yellow_0(esk1_0,X1)
    | ~ r2_lattice3(esk1_0,X1,esk13_3(esk1_0,esk2_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_21]),c_0_52])])).

cnf(c_0_94,negated_conjecture,
    ( r1_yellow_0(esk1_0,esk3_0)
    | v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_89]),c_0_78]),c_0_21]),c_0_20]),c_0_52]),c_0_26]),c_0_53])])).

cnf(c_0_95,negated_conjecture,
    ( r2_lattice3(X1,esk3_0,esk13_3(X1,esk2_0,esk3_0))
    | v2_struct_0(X1)
    | ~ v1_waybel_0(esk2_0,X1)
    | ~ m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ v4_orders_2(X1) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_90,c_0_77]),c_0_78])]),c_0_64])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk1_0,X1),esk2_0)
    | ~ r1_orders_2(esk1_0,k1_yellow_0(esk1_0,X1),X2)
    | ~ r2_hidden(X2,esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_24]),c_0_92]),c_0_21])])).

cnf(c_0_97,negated_conjecture,
    ( r1_orders_2(esk1_0,k1_yellow_0(esk1_0,esk3_0),esk13_3(esk1_0,esk2_0,esk3_0))
    | v1_xboole_0(esk3_0)
    | ~ r2_lattice3(esk1_0,esk3_0,esk13_3(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_93,c_0_94])).

cnf(c_0_98,negated_conjecture,
    ( r2_lattice3(esk1_0,esk3_0,esk13_3(esk1_0,esk2_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_95,c_0_74]),c_0_24]),c_0_21]),c_0_26])]),c_0_27])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk1_0,esk3_0),esk2_0)
    | ~ v1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(k1_yellow_0(esk1_0,X1),esk2_0)
    | ~ r1_orders_2(esk1_0,k1_yellow_0(esk1_0,X1),esk13_3(esk1_0,esk2_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_96,c_0_84])).

cnf(c_0_101,negated_conjecture,
    ( r1_orders_2(esk1_0,k1_yellow_0(esk1_0,esk3_0),esk13_3(esk1_0,esk2_0,esk3_0))
    | v1_xboole_0(esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_98])])).

cnf(c_0_102,negated_conjecture,
    ( ~ r2_hidden(k1_yellow_0(esk1_0,esk3_0),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_99,c_0_74])])).

cnf(c_0_103,negated_conjecture,
    ( esk3_0 != k1_xboole_0
    | ~ v1_waybel_0(esk2_0,esk1_0) ),
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
