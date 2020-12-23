%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_7__t28_waybel_7.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:05 EDT 2019

% Result     : Theorem 74.98s
% Output     : CNFRefutation 74.98s
% Verified   : 
% Statistics : Number of formulae       :  109 (2405 expanded)
%              Number of clauses        :   82 ( 807 expanded)
%              Number of leaves         :   13 ( 592 expanded)
%              Depth                    :   15
%              Number of atoms          :  683 (29459 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   27 (   6 average)
%              Maximal clause size      :  119 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t28_waybel_7,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ~ ( ~ r2_hidden(X3,X2)
                  & ! [X4] :
                      ( ( ~ v1_xboole_0(X4)
                        & v1_waybel_0(X4,X1)
                        & v12_waybel_0(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                     => ~ ( v1_waybel_7(X4,X1)
                          & r1_tarski(X2,X4)
                          & ~ r2_hidden(X3,X4) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',t28_waybel_7)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',cc2_lattice3)).

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
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',d19_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',t4_subset)).

fof(dt_k6_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',dt_k6_waybel_0)).

fof(t18_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_hidden(X3,k6_waybel_0(X1,X2))
              <=> r1_orders_2(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',t18_waybel_0)).

fof(fc9_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ~ v1_xboole_0(k6_waybel_0(X1,X2))
        & v2_waybel_0(k6_waybel_0(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',fc9_waybel_0)).

fof(fc13_waybel_0,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1)) )
     => v13_waybel_0(k6_waybel_0(X1,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',fc13_waybel_0)).

fof(t3_xboole_0,axiom,(
    ! [X1,X2] :
      ( ~ ( ~ r1_xboole_0(X1,X2)
          & ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X2) ) )
      & ~ ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(X3,X2) )
          & r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',t3_xboole_0)).

fof(t27_waybel_7,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v2_waybel_1(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v1_waybel_0(X2,X1)
            & v12_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ! [X3] :
              ( ( ~ v1_xboole_0(X3)
                & v2_waybel_0(X3,X1)
                & v13_waybel_0(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
             => ~ ( r1_subset_1(X2,X3)
                  & ! [X4] :
                      ( ( ~ v1_xboole_0(X4)
                        & v1_waybel_0(X4,X1)
                        & v12_waybel_0(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                     => ~ ( v1_waybel_7(X4,X1)
                          & r1_tarski(X2,X4)
                          & r1_subset_1(X4,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',t27_waybel_7)).

fof(redefinition_r1_subset_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X2) )
     => ( r1_subset_1(X1,X2)
      <=> r1_xboole_0(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',redefinition_r1_subset_1)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',reflexivity_r3_orders_2)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_7__t28_waybel_7.p',redefinition_r3_orders_2)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v2_waybel_1(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v1_waybel_0(X2,X1)
              & v12_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( ~ r2_hidden(X3,X2)
                    & ! [X4] :
                        ( ( ~ v1_xboole_0(X4)
                          & v1_waybel_0(X4,X1)
                          & v12_waybel_0(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                       => ~ ( v1_waybel_7(X4,X1)
                            & r1_tarski(X2,X4)
                            & ~ r2_hidden(X3,X4) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t28_waybel_7])).

fof(c_0_14,plain,(
    ! [X74] :
      ( ~ l1_orders_2(X74)
      | ~ v2_lattice3(X74)
      | ~ v2_struct_0(X74) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_15,negated_conjecture,(
    ! [X8] :
      ( v3_orders_2(esk1_0)
      & v4_orders_2(esk1_0)
      & v5_orders_2(esk1_0)
      & v2_waybel_1(esk1_0)
      & v1_lattice3(esk1_0)
      & v2_lattice3(esk1_0)
      & l1_orders_2(esk1_0)
      & ~ v1_xboole_0(esk2_0)
      & v1_waybel_0(esk2_0,esk1_0)
      & v12_waybel_0(esk2_0,esk1_0)
      & m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0)))
      & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
      & ~ r2_hidden(esk3_0,esk2_0)
      & ( v1_xboole_0(X8)
        | ~ v1_waybel_0(X8,esk1_0)
        | ~ v12_waybel_0(X8,esk1_0)
        | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ v1_waybel_7(X8,esk1_0)
        | ~ r1_tarski(esk2_0,X8)
        | r2_hidden(esk3_0,X8) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])])).

fof(c_0_16,plain,(
    ! [X11,X12,X13,X14] :
      ( ( ~ v12_waybel_0(X12,X11)
        | ~ m1_subset_1(X13,u1_struct_0(X11))
        | ~ m1_subset_1(X14,u1_struct_0(X11))
        | ~ r2_hidden(X13,X12)
        | ~ r1_orders_2(X11,X14,X13)
        | r2_hidden(X14,X12)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk4_2(X11,X12),u1_struct_0(X11))
        | v12_waybel_0(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_orders_2(X11) )
      & ( m1_subset_1(esk5_2(X11,X12),u1_struct_0(X11))
        | v12_waybel_0(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_orders_2(X11) )
      & ( r2_hidden(esk4_2(X11,X12),X12)
        | v12_waybel_0(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_orders_2(X11) )
      & ( r1_orders_2(X11,esk5_2(X11,X12),esk4_2(X11,X12))
        | v12_waybel_0(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_orders_2(X11) )
      & ( ~ r2_hidden(esk5_2(X11,X12),X12)
        | v12_waybel_0(X12,X11)
        | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(X11)))
        | ~ l1_orders_2(X11) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d19_waybel_0])])])])])).

fof(c_0_17,plain,(
    ! [X63,X64,X65] :
      ( ~ r2_hidden(X63,X64)
      | ~ m1_subset_1(X64,k1_zfmisc_1(X65))
      | m1_subset_1(X63,X65) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_18,plain,(
    ! [X21,X22] :
      ( v2_struct_0(X21)
      | ~ l1_orders_2(X21)
      | ~ m1_subset_1(X22,u1_struct_0(X21))
      | m1_subset_1(k6_waybel_0(X21,X22),k1_zfmisc_1(u1_struct_0(X21))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_waybel_0])])])).

cnf(c_0_19,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_20,negated_conjecture,
    ( v2_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_21,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_22,plain,
    ( r2_hidden(X4,X1)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X4,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(k6_waybel_0(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_26,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])])).

cnf(c_0_27,plain,
    ( r2_hidden(X1,X2)
    | ~ r1_orders_2(X3,X1,X4)
    | ~ r2_hidden(X4,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ v12_waybel_0(X2,X3)
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_28,plain,(
    ! [X44,X45,X46] :
      ( ( ~ r2_hidden(X46,k6_waybel_0(X44,X45))
        | r1_orders_2(X44,X45,X46)
        | ~ m1_subset_1(X46,u1_struct_0(X44))
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ l1_orders_2(X44) )
      & ( ~ r1_orders_2(X44,X45,X46)
        | r2_hidden(X46,k6_waybel_0(X44,X45))
        | ~ m1_subset_1(X46,u1_struct_0(X44))
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | v2_struct_0(X44)
        | ~ l1_orders_2(X44) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t18_waybel_0])])])])])).

cnf(c_0_29,negated_conjecture,
    ( m1_subset_1(k6_waybel_0(esk1_0,esk3_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_21])]),c_0_26])).

fof(c_0_30,plain,(
    ! [X77,X78] :
      ( ( ~ v1_xboole_0(k6_waybel_0(X77,X78))
        | v2_struct_0(X77)
        | ~ v3_orders_2(X77)
        | ~ l1_orders_2(X77)
        | ~ m1_subset_1(X78,u1_struct_0(X77)) )
      & ( v2_waybel_0(k6_waybel_0(X77,X78),X77)
        | v2_struct_0(X77)
        | ~ v3_orders_2(X77)
        | ~ l1_orders_2(X77)
        | ~ m1_subset_1(X78,u1_struct_0(X77)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc9_waybel_0])])])])).

fof(c_0_31,plain,(
    ! [X75,X76] :
      ( v2_struct_0(X75)
      | ~ v4_orders_2(X75)
      | ~ l1_orders_2(X75)
      | ~ m1_subset_1(X76,u1_struct_0(X75))
      | v13_waybel_0(k6_waybel_0(X75,X76),X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc13_waybel_0])])])).

cnf(c_0_32,negated_conjecture,
    ( r2_hidden(esk3_0,X1)
    | ~ r1_orders_2(esk1_0,esk3_0,X2)
    | ~ r2_hidden(X2,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v12_waybel_0(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_27,c_0_25]),c_0_21])])).

cnf(c_0_33,negated_conjecture,
    ( v12_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_34,negated_conjecture,
    ( m1_subset_1(esk2_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_35,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_36,plain,(
    ! [X57,X58,X60,X61,X62] :
      ( ( r2_hidden(esk10_2(X57,X58),X57)
        | r1_xboole_0(X57,X58) )
      & ( r2_hidden(esk10_2(X57,X58),X58)
        | r1_xboole_0(X57,X58) )
      & ( ~ r2_hidden(X62,X60)
        | ~ r2_hidden(X62,X61)
        | ~ r1_xboole_0(X60,X61) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_37,plain,
    ( r1_orders_2(X2,X3,X1)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,k6_waybel_0(X2,X3))
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_23,c_0_29])).

fof(c_0_39,plain,(
    ! [X49,X50,X51] :
      ( ( ~ v1_xboole_0(esk9_3(X49,X50,X51))
        | ~ r1_subset_1(X50,X51)
        | v1_xboole_0(X51)
        | ~ v2_waybel_0(X51,X49)
        | ~ v13_waybel_0(X51,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | v1_xboole_0(X50)
        | ~ v1_waybel_0(X50,X49)
        | ~ v12_waybel_0(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ v3_orders_2(X49)
        | ~ v4_orders_2(X49)
        | ~ v5_orders_2(X49)
        | ~ v2_waybel_1(X49)
        | ~ v1_lattice3(X49)
        | ~ v2_lattice3(X49)
        | ~ l1_orders_2(X49) )
      & ( v1_waybel_0(esk9_3(X49,X50,X51),X49)
        | ~ r1_subset_1(X50,X51)
        | v1_xboole_0(X51)
        | ~ v2_waybel_0(X51,X49)
        | ~ v13_waybel_0(X51,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | v1_xboole_0(X50)
        | ~ v1_waybel_0(X50,X49)
        | ~ v12_waybel_0(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ v3_orders_2(X49)
        | ~ v4_orders_2(X49)
        | ~ v5_orders_2(X49)
        | ~ v2_waybel_1(X49)
        | ~ v1_lattice3(X49)
        | ~ v2_lattice3(X49)
        | ~ l1_orders_2(X49) )
      & ( v12_waybel_0(esk9_3(X49,X50,X51),X49)
        | ~ r1_subset_1(X50,X51)
        | v1_xboole_0(X51)
        | ~ v2_waybel_0(X51,X49)
        | ~ v13_waybel_0(X51,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | v1_xboole_0(X50)
        | ~ v1_waybel_0(X50,X49)
        | ~ v12_waybel_0(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ v3_orders_2(X49)
        | ~ v4_orders_2(X49)
        | ~ v5_orders_2(X49)
        | ~ v2_waybel_1(X49)
        | ~ v1_lattice3(X49)
        | ~ v2_lattice3(X49)
        | ~ l1_orders_2(X49) )
      & ( m1_subset_1(esk9_3(X49,X50,X51),k1_zfmisc_1(u1_struct_0(X49)))
        | ~ r1_subset_1(X50,X51)
        | v1_xboole_0(X51)
        | ~ v2_waybel_0(X51,X49)
        | ~ v13_waybel_0(X51,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | v1_xboole_0(X50)
        | ~ v1_waybel_0(X50,X49)
        | ~ v12_waybel_0(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ v3_orders_2(X49)
        | ~ v4_orders_2(X49)
        | ~ v5_orders_2(X49)
        | ~ v2_waybel_1(X49)
        | ~ v1_lattice3(X49)
        | ~ v2_lattice3(X49)
        | ~ l1_orders_2(X49) )
      & ( v1_waybel_7(esk9_3(X49,X50,X51),X49)
        | ~ r1_subset_1(X50,X51)
        | v1_xboole_0(X51)
        | ~ v2_waybel_0(X51,X49)
        | ~ v13_waybel_0(X51,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | v1_xboole_0(X50)
        | ~ v1_waybel_0(X50,X49)
        | ~ v12_waybel_0(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ v3_orders_2(X49)
        | ~ v4_orders_2(X49)
        | ~ v5_orders_2(X49)
        | ~ v2_waybel_1(X49)
        | ~ v1_lattice3(X49)
        | ~ v2_lattice3(X49)
        | ~ l1_orders_2(X49) )
      & ( r1_tarski(X50,esk9_3(X49,X50,X51))
        | ~ r1_subset_1(X50,X51)
        | v1_xboole_0(X51)
        | ~ v2_waybel_0(X51,X49)
        | ~ v13_waybel_0(X51,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | v1_xboole_0(X50)
        | ~ v1_waybel_0(X50,X49)
        | ~ v12_waybel_0(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ v3_orders_2(X49)
        | ~ v4_orders_2(X49)
        | ~ v5_orders_2(X49)
        | ~ v2_waybel_1(X49)
        | ~ v1_lattice3(X49)
        | ~ v2_lattice3(X49)
        | ~ l1_orders_2(X49) )
      & ( r1_subset_1(esk9_3(X49,X50,X51),X51)
        | ~ r1_subset_1(X50,X51)
        | v1_xboole_0(X51)
        | ~ v2_waybel_0(X51,X49)
        | ~ v13_waybel_0(X51,X49)
        | ~ m1_subset_1(X51,k1_zfmisc_1(u1_struct_0(X49)))
        | v1_xboole_0(X50)
        | ~ v1_waybel_0(X50,X49)
        | ~ v12_waybel_0(X50,X49)
        | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X49)))
        | ~ v3_orders_2(X49)
        | ~ v4_orders_2(X49)
        | ~ v5_orders_2(X49)
        | ~ v2_waybel_1(X49)
        | ~ v1_lattice3(X49)
        | ~ v2_lattice3(X49)
        | ~ l1_orders_2(X49) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t27_waybel_7])])])])])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(k6_waybel_0(X1,X2))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | v13_waybel_0(k6_waybel_0(X1,X2),X1)
    | ~ v4_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_44,plain,
    ( v2_waybel_0(k6_waybel_0(X1,X2),X1)
    | v2_struct_0(X1)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_45,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_0,X1)
    | ~ r2_hidden(X1,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34])]),c_0_35])).

cnf(c_0_46,plain,
    ( r2_hidden(esk10_2(X1,X2),X1)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_47,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,X1)
    | ~ r2_hidden(X1,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_25]),c_0_21])]),c_0_26]),c_0_38])).

cnf(c_0_48,plain,
    ( r2_hidden(esk10_2(X1,X2),X2)
    | r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_49,plain,
    ( r1_subset_1(esk9_3(X1,X2,X3),X3)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_50,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_51,negated_conjecture,
    ( v2_waybel_1(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_52,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_53,negated_conjecture,
    ( ~ v1_xboole_0(k6_waybel_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_25]),c_0_21]),c_0_41])]),c_0_26])).

cnf(c_0_54,negated_conjecture,
    ( v13_waybel_0(k6_waybel_0(esk1_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_25]),c_0_21]),c_0_43])]),c_0_26])).

cnf(c_0_55,negated_conjecture,
    ( v2_waybel_0(k6_waybel_0(esk1_0,esk3_0),esk1_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_25]),c_0_21]),c_0_41])]),c_0_26])).

fof(c_0_56,plain,(
    ! [X32,X33] :
      ( ( ~ r1_subset_1(X32,X33)
        | r1_xboole_0(X32,X33)
        | v1_xboole_0(X32)
        | v1_xboole_0(X33) )
      & ( ~ r1_xboole_0(X32,X33)
        | r1_subset_1(X32,X33)
        | v1_xboole_0(X32)
        | v1_xboole_0(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r1_subset_1])])])])).

cnf(c_0_57,negated_conjecture,
    ( r1_xboole_0(esk2_0,X1)
    | ~ r1_orders_2(esk1_0,esk3_0,esk10_2(esk2_0,X1)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_58,negated_conjecture,
    ( r1_xboole_0(X1,k6_waybel_0(esk1_0,esk3_0))
    | r1_orders_2(esk1_0,esk3_0,esk10_2(X1,k6_waybel_0(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_59,plain,
    ( v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ v1_xboole_0(esk9_3(X1,X2,X3))
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

fof(c_0_60,plain,(
    ! [X37,X38,X39] :
      ( v2_struct_0(X37)
      | ~ v3_orders_2(X37)
      | ~ l1_orders_2(X37)
      | ~ m1_subset_1(X38,u1_struct_0(X37))
      | ~ m1_subset_1(X39,u1_struct_0(X37))
      | r3_orders_2(X37,X38,X38) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_61,negated_conjecture,
    ( r1_subset_1(esk9_3(esk1_0,X1,k6_waybel_0(esk1_0,esk3_0)),k6_waybel_0(esk1_0,esk3_0))
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,k6_waybel_0(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v12_waybel_0(X1,esk1_0)
    | ~ v1_waybel_0(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_49,c_0_29]),c_0_21]),c_0_20]),c_0_50]),c_0_51]),c_0_52]),c_0_43]),c_0_41])]),c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_62,negated_conjecture,
    ( v1_waybel_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_64,plain,
    ( r1_subset_1(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_xboole_0(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_65,negated_conjecture,
    ( r1_xboole_0(esk2_0,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_57,c_0_58])).

cnf(c_0_66,negated_conjecture,
    ( v1_xboole_0(X1)
    | ~ r1_subset_1(X1,k6_waybel_0(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v12_waybel_0(X1,esk1_0)
    | ~ v1_waybel_0(X1,esk1_0)
    | ~ v1_xboole_0(esk9_3(esk1_0,X1,k6_waybel_0(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_29]),c_0_21]),c_0_20]),c_0_50]),c_0_51]),c_0_52]),c_0_43]),c_0_41])]),c_0_53]),c_0_54]),c_0_55])])).

fof(c_0_67,plain,(
    ! [X34,X35,X36] :
      ( ( ~ r3_orders_2(X34,X35,X36)
        | r1_orders_2(X34,X35,X36)
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ l1_orders_2(X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | ~ m1_subset_1(X36,u1_struct_0(X34)) )
      & ( ~ r1_orders_2(X34,X35,X36)
        | r3_orders_2(X34,X35,X36)
        | v2_struct_0(X34)
        | ~ v3_orders_2(X34)
        | ~ l1_orders_2(X34)
        | ~ m1_subset_1(X35,u1_struct_0(X34))
        | ~ m1_subset_1(X36,u1_struct_0(X34)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_68,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_60])).

cnf(c_0_69,negated_conjecture,
    ( r1_subset_1(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)),k6_waybel_0(esk1_0,esk3_0))
    | ~ r1_subset_1(esk2_0,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_33]),c_0_34]),c_0_62])]),c_0_63])).

cnf(c_0_70,negated_conjecture,
    ( r1_subset_1(esk2_0,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_63]),c_0_53])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_subset_1(esk2_0,k6_waybel_0(esk1_0,esk3_0))
    | ~ v1_xboole_0(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_33]),c_0_34]),c_0_62])]),c_0_63])).

cnf(c_0_72,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_73,plain,
    ( r3_orders_2(X1,X2,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(condense,[status(thm)],[c_0_68])).

cnf(c_0_74,plain,
    ( r1_tarski(X1,esk9_3(X2,X1,X3))
    | v1_xboole_0(X3)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,X3)
    | ~ v2_waybel_0(X3,X2)
    | ~ v13_waybel_0(X3,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v1_waybel_0(X1,X2)
    | ~ v12_waybel_0(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v2_waybel_1(X2)
    | ~ v1_lattice3(X2)
    | ~ v2_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_75,plain,
    ( v1_waybel_7(esk9_3(X1,X2,X3),X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_76,plain,
    ( m1_subset_1(esk9_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_77,plain,
    ( v12_waybel_0(esk9_3(X1,X2,X3),X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_78,plain,
    ( v1_waybel_0(esk9_3(X1,X2,X3),X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X2,X3)
    | ~ v2_waybel_0(X3,X1)
    | ~ v13_waybel_0(X3,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v1_waybel_0(X2,X1)
    | ~ v12_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v2_waybel_1(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_79,plain,
    ( r1_xboole_0(X1,X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | ~ r1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_80,negated_conjecture,
    ( r1_subset_1(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)),k6_waybel_0(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_69,c_0_70])])).

cnf(c_0_81,negated_conjecture,
    ( ~ v1_xboole_0(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_71,c_0_70])])).

cnf(c_0_82,plain,
    ( r2_hidden(X3,k6_waybel_0(X1,X2))
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_83,negated_conjecture,
    ( r1_orders_2(esk1_0,X1,esk3_0)
    | ~ r3_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_25]),c_0_21]),c_0_41])]),c_0_26])).

cnf(c_0_84,negated_conjecture,
    ( r3_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_25]),c_0_21]),c_0_41])]),c_0_26])).

cnf(c_0_85,negated_conjecture,
    ( r1_tarski(X1,esk9_3(esk1_0,X1,k6_waybel_0(esk1_0,esk3_0)))
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,k6_waybel_0(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v12_waybel_0(X1,esk1_0)
    | ~ v1_waybel_0(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_29]),c_0_21]),c_0_20]),c_0_50]),c_0_51]),c_0_52]),c_0_43]),c_0_41])]),c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_86,negated_conjecture,
    ( v1_waybel_7(esk9_3(esk1_0,X1,k6_waybel_0(esk1_0,esk3_0)),esk1_0)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,k6_waybel_0(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v12_waybel_0(X1,esk1_0)
    | ~ v1_waybel_0(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_29]),c_0_21]),c_0_20]),c_0_50]),c_0_51]),c_0_52]),c_0_43]),c_0_41])]),c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_87,negated_conjecture,
    ( m1_subset_1(esk9_3(esk1_0,X1,k6_waybel_0(esk1_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,k6_waybel_0(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v12_waybel_0(X1,esk1_0)
    | ~ v1_waybel_0(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_29]),c_0_21]),c_0_20]),c_0_50]),c_0_51]),c_0_52]),c_0_43]),c_0_41])]),c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_88,negated_conjecture,
    ( v12_waybel_0(esk9_3(esk1_0,X1,k6_waybel_0(esk1_0,esk3_0)),esk1_0)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,k6_waybel_0(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v12_waybel_0(X1,esk1_0)
    | ~ v1_waybel_0(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_29]),c_0_21]),c_0_20]),c_0_50]),c_0_51]),c_0_52]),c_0_43]),c_0_41])]),c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_89,negated_conjecture,
    ( v1_waybel_0(esk9_3(esk1_0,X1,k6_waybel_0(esk1_0,esk3_0)),esk1_0)
    | v1_xboole_0(X1)
    | ~ r1_subset_1(X1,k6_waybel_0(esk1_0,esk3_0))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v12_waybel_0(X1,esk1_0)
    | ~ v1_waybel_0(X1,esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_29]),c_0_21]),c_0_20]),c_0_50]),c_0_51]),c_0_52]),c_0_43]),c_0_41])]),c_0_53]),c_0_54]),c_0_55])])).

cnf(c_0_90,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_91,negated_conjecture,
    ( r1_xboole_0(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)),k6_waybel_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_81]),c_0_53])).

cnf(c_0_92,negated_conjecture,
    ( r2_hidden(esk3_0,k6_waybel_0(esk1_0,X1))
    | ~ r1_orders_2(esk1_0,X1,esk3_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_82,c_0_25]),c_0_21])]),c_0_26])).

cnf(c_0_93,negated_conjecture,
    ( r1_orders_2(esk1_0,esk3_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_25])])).

cnf(c_0_94,negated_conjecture,
    ( r1_tarski(esk2_0,esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)))
    | ~ r1_subset_1(esk2_0,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_33]),c_0_34]),c_0_62])]),c_0_63])).

cnf(c_0_95,negated_conjecture,
    ( v1_waybel_7(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)),esk1_0)
    | ~ r1_subset_1(esk2_0,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_86,c_0_33]),c_0_34]),c_0_62])]),c_0_63])).

cnf(c_0_96,negated_conjecture,
    ( m1_subset_1(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r1_subset_1(esk2_0,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_33]),c_0_34]),c_0_62])]),c_0_63])).

cnf(c_0_97,negated_conjecture,
    ( v12_waybel_0(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)),esk1_0)
    | ~ r1_subset_1(esk2_0,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_88,c_0_62]),c_0_34]),c_0_33])]),c_0_63])).

cnf(c_0_98,negated_conjecture,
    ( v1_waybel_0(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)),esk1_0)
    | ~ r1_subset_1(esk2_0,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_33]),c_0_34]),c_0_62])]),c_0_63])).

cnf(c_0_99,negated_conjecture,
    ( ~ r2_hidden(X1,esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)))
    | ~ r2_hidden(X1,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(spm,[status(thm)],[c_0_90,c_0_91])).

cnf(c_0_100,negated_conjecture,
    ( r2_hidden(esk3_0,k6_waybel_0(esk1_0,esk3_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_25])])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(X1)
    | r2_hidden(esk3_0,X1)
    | ~ v1_waybel_0(X1,esk1_0)
    | ~ v12_waybel_0(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ v1_waybel_7(X1,esk1_0)
    | ~ r1_tarski(esk2_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_102,negated_conjecture,
    ( r1_tarski(esk2_0,esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_94,c_0_70])])).

cnf(c_0_103,negated_conjecture,
    ( v1_waybel_7(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_95,c_0_70])])).

cnf(c_0_104,negated_conjecture,
    ( m1_subset_1(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_96,c_0_70])])).

cnf(c_0_105,negated_conjecture,
    ( v12_waybel_0(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_97,c_0_70])])).

cnf(c_0_106,negated_conjecture,
    ( v1_waybel_0(esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0)),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_98,c_0_70])])).

cnf(c_0_107,negated_conjecture,
    ( ~ r2_hidden(esk3_0,esk9_3(esk1_0,esk2_0,k6_waybel_0(esk1_0,esk3_0))) ),
    inference(spm,[status(thm)],[c_0_99,c_0_100])).

cnf(c_0_108,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_81]),c_0_103]),c_0_104]),c_0_105]),c_0_106])]),c_0_107]),
    [proof]).
%------------------------------------------------------------------------------
