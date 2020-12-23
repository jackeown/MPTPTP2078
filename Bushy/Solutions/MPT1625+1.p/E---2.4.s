%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : waybel_0__t5_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:00 EDT 2019

% Result     : Theorem 0.86s
% Output     : CNFRefutation 0.86s
% Verified   : 
% Statistics : Number of formulae       :   99 (6126 expanded)
%              Number of clauses        :   72 (2388 expanded)
%              Number of leaves         :   13 (1500 expanded)
%              Depth                    :   26
%              Number of atoms          :  412 (25050 expanded)
%              Number of equality atoms :   41 ( 934 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   55 (   2 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t5_waybel_0,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( v1_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1)
            & v2_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',t5_waybel_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',t2_subset)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',dt_l1_orders_2)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',t7_boole)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',redefinition_k6_domain_1)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',dt_k6_domain_1)).

fof(d1_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v1_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ~ ( r2_hidden(X5,X2)
                                & r1_orders_2(X1,X3,X5)
                                & r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',d1_waybel_0)).

fof(d2_waybel_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_waybel_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ~ ( r2_hidden(X3,X2)
                        & r2_hidden(X4,X2)
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => ~ ( r2_hidden(X5,X2)
                                & r1_orders_2(X1,X5,X3)
                                & r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',d2_waybel_0)).

fof(d1_tarski,axiom,(
    ! [X1,X2] :
      ( X2 = k1_tarski(X1)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> X3 = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',d1_tarski)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',reflexivity_r3_orders_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',t4_subset)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t5_waybel_0.p',redefinition_r3_orders_2)).

fof(c_0_13,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( v1_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1)
              & v2_waybel_0(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ) ),
    inference(assume_negation,[status(cth)],[t5_waybel_0])).

fof(c_0_14,plain,(
    ! [X52,X53] :
      ( ~ m1_subset_1(X52,X53)
      | v1_xboole_0(X53)
      | r2_hidden(X52,X53) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_15,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    & v3_orders_2(esk1_0)
    & l1_orders_2(esk1_0)
    & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
    & ( ~ v1_waybel_0(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
      | ~ v2_waybel_0(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_13])])])])).

fof(c_0_16,plain,(
    ! [X40] :
      ( v2_struct_0(X40)
      | ~ l1_struct_0(X40)
      | ~ v1_xboole_0(u1_struct_0(X40)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_17,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_19,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_20,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_17,c_0_18])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_22,plain,(
    ! [X35] :
      ( ~ l1_orders_2(X35)
      | l1_struct_0(X35) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_23,plain,(
    ! [X63,X64] :
      ( ~ r2_hidden(X63,X64)
      | ~ v1_xboole_0(X64) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_24,negated_conjecture,
    ( r2_hidden(esk2_0,u1_struct_0(esk1_0))
    | ~ l1_struct_0(esk1_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_19,c_0_20]),c_0_21])).

cnf(c_0_25,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_26,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_27,plain,(
    ! [X42,X43] :
      ( v1_xboole_0(X42)
      | ~ m1_subset_1(X43,X42)
      | k6_domain_1(X42,X43) = k1_tarski(X43) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_28,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,negated_conjecture,
    ( r2_hidden(esk2_0,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

fof(c_0_30,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X33)
      | ~ m1_subset_1(X34,X33)
      | m1_subset_1(k6_domain_1(X33,X34),k1_zfmisc_1(X33)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_31,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_28,c_0_29])).

fof(c_0_33,plain,(
    ! [X17,X18,X19,X20,X24] :
      ( ( m1_subset_1(esk4_4(X17,X18,X19,X20),u1_struct_0(X17))
        | ~ r2_hidden(X19,X18)
        | ~ r2_hidden(X20,X18)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ v1_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( r2_hidden(esk4_4(X17,X18,X19,X20),X18)
        | ~ r2_hidden(X19,X18)
        | ~ r2_hidden(X20,X18)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ v1_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X19,esk4_4(X17,X18,X19,X20))
        | ~ r2_hidden(X19,X18)
        | ~ r2_hidden(X20,X18)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ v1_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( r1_orders_2(X17,X20,esk4_4(X17,X18,X19,X20))
        | ~ r2_hidden(X19,X18)
        | ~ r2_hidden(X20,X18)
        | ~ m1_subset_1(X20,u1_struct_0(X17))
        | ~ m1_subset_1(X19,u1_struct_0(X17))
        | ~ v1_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk5_2(X17,X18),u1_struct_0(X17))
        | v1_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( m1_subset_1(esk6_2(X17,X18),u1_struct_0(X17))
        | v1_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( r2_hidden(esk5_2(X17,X18),X18)
        | v1_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( r2_hidden(esk6_2(X17,X18),X18)
        | v1_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( ~ m1_subset_1(X24,u1_struct_0(X17))
        | ~ r2_hidden(X24,X18)
        | ~ r1_orders_2(X17,esk5_2(X17,X18),X24)
        | ~ r1_orders_2(X17,esk6_2(X17,X18),X24)
        | v1_waybel_0(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_waybel_0])])])])])).

cnf(c_0_34,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk1_0),esk2_0) = k1_tarski(esk2_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_18]),c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( ~ v1_waybel_0(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0)
    | ~ v2_waybel_0(k6_domain_1(u1_struct_0(esk1_0),esk2_0),esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_37,plain,
    ( r2_hidden(esk5_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(k1_tarski(esk2_0),k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_18]),c_0_35]),c_0_32])).

fof(c_0_39,plain,(
    ! [X25,X26,X27,X28,X32] :
      ( ( m1_subset_1(esk7_4(X25,X26,X27,X28),u1_struct_0(X25))
        | ~ r2_hidden(X27,X26)
        | ~ r2_hidden(X28,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ v2_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( r2_hidden(esk7_4(X25,X26,X27,X28),X26)
        | ~ r2_hidden(X27,X26)
        | ~ r2_hidden(X28,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ v2_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( r1_orders_2(X25,esk7_4(X25,X26,X27,X28),X27)
        | ~ r2_hidden(X27,X26)
        | ~ r2_hidden(X28,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ v2_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( r1_orders_2(X25,esk7_4(X25,X26,X27,X28),X28)
        | ~ r2_hidden(X27,X26)
        | ~ r2_hidden(X28,X26)
        | ~ m1_subset_1(X28,u1_struct_0(X25))
        | ~ m1_subset_1(X27,u1_struct_0(X25))
        | ~ v2_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(esk8_2(X25,X26),u1_struct_0(X25))
        | v2_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( m1_subset_1(esk9_2(X25,X26),u1_struct_0(X25))
        | v2_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( r2_hidden(esk8_2(X25,X26),X26)
        | v2_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( r2_hidden(esk9_2(X25,X26),X26)
        | v2_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) )
      & ( ~ m1_subset_1(X32,u1_struct_0(X25))
        | ~ r2_hidden(X32,X26)
        | ~ r1_orders_2(X25,X32,esk8_2(X25,X26))
        | ~ r1_orders_2(X25,X32,esk9_2(X25,X26))
        | v2_waybel_0(X26,X25)
        | ~ m1_subset_1(X26,k1_zfmisc_1(u1_struct_0(X25)))
        | ~ l1_orders_2(X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_waybel_0])])])])])).

fof(c_0_40,plain,(
    ! [X10,X11,X12,X13,X14,X15] :
      ( ( ~ r2_hidden(X12,X11)
        | X12 = X10
        | X11 != k1_tarski(X10) )
      & ( X13 != X10
        | r2_hidden(X13,X11)
        | X11 != k1_tarski(X10) )
      & ( ~ r2_hidden(esk3_2(X14,X15),X15)
        | esk3_2(X14,X15) != X14
        | X15 = k1_tarski(X14) )
      & ( r2_hidden(esk3_2(X14,X15),X15)
        | esk3_2(X14,X15) = X14
        | X15 = k1_tarski(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_tarski])])])])])])).

cnf(c_0_41,negated_conjecture,
    ( ~ v2_waybel_0(k1_tarski(esk2_0),esk1_0)
    | ~ v1_waybel_0(k1_tarski(esk2_0),esk1_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_36,c_0_35]),c_0_35])).

cnf(c_0_42,negated_conjecture,
    ( r2_hidden(esk5_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0))
    | v1_waybel_0(k1_tarski(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_26])])).

cnf(c_0_43,plain,
    ( r2_hidden(esk8_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_44,plain,
    ( X1 = X3
    | ~ r2_hidden(X1,X2)
    | X2 != k1_tarski(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_45,negated_conjecture,
    ( r2_hidden(esk5_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0))
    | ~ v2_waybel_0(k1_tarski(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_46,negated_conjecture,
    ( r2_hidden(esk8_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0))
    | v2_waybel_0(k1_tarski(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_38]),c_0_26])])).

fof(c_0_47,plain,(
    ! [X47,X48,X49] :
      ( v2_struct_0(X47)
      | ~ v3_orders_2(X47)
      | ~ l1_orders_2(X47)
      | ~ m1_subset_1(X48,u1_struct_0(X47))
      | ~ m1_subset_1(X49,u1_struct_0(X47))
      | r3_orders_2(X47,X48,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_48,plain,
    ( r2_hidden(esk6_2(X1,X2),X2)
    | v1_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

fof(c_0_49,plain,(
    ! [X56,X57,X58] :
      ( ~ r2_hidden(X56,X57)
      | ~ m1_subset_1(X57,k1_zfmisc_1(X58))
      | m1_subset_1(X56,X58) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_50,plain,
    ( X1 = X2
    | ~ r2_hidden(X1,k1_tarski(X2)) ),
    inference(er,[status(thm)],[c_0_44])).

cnf(c_0_51,negated_conjecture,
    ( r2_hidden(esk8_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0))
    | r2_hidden(esk5_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_52,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_53,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

cnf(c_0_54,plain,
    ( r2_hidden(esk9_2(X1,X2),X2)
    | v2_waybel_0(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_55,negated_conjecture,
    ( r2_hidden(esk6_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0))
    | v1_waybel_0(k1_tarski(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_38]),c_0_26])])).

cnf(c_0_56,plain,
    ( v2_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X2,X1,esk8_2(X2,X3))
    | ~ r1_orders_2(X2,X1,esk9_2(X2,X3))
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_58,negated_conjecture,
    ( esk8_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | r2_hidden(esk5_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

fof(c_0_59,plain,(
    ! [X44,X45,X46] :
      ( ( ~ r3_orders_2(X44,X45,X46)
        | r1_orders_2(X44,X45,X46)
        | v2_struct_0(X44)
        | ~ v3_orders_2(X44)
        | ~ l1_orders_2(X44)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | ~ m1_subset_1(X46,u1_struct_0(X44)) )
      & ( ~ r1_orders_2(X44,X45,X46)
        | r3_orders_2(X44,X45,X46)
        | v2_struct_0(X44)
        | ~ v3_orders_2(X44)
        | ~ l1_orders_2(X44)
        | ~ m1_subset_1(X45,u1_struct_0(X44))
        | ~ m1_subset_1(X46,u1_struct_0(X44)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_60,negated_conjecture,
    ( r3_orders_2(esk1_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_52,c_0_18]),c_0_26]),c_0_53])]),c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( r2_hidden(esk9_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0))
    | v2_waybel_0(k1_tarski(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_38]),c_0_26])])).

cnf(c_0_62,negated_conjecture,
    ( r2_hidden(esk6_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0))
    | ~ v2_waybel_0(k1_tarski(esk2_0),esk1_0) ),
    inference(spm,[status(thm)],[c_0_41,c_0_55])).

cnf(c_0_63,plain,
    ( v2_waybel_0(X1,X2)
    | ~ r1_orders_2(X2,X3,esk8_2(X2,X1))
    | ~ r1_orders_2(X2,X3,esk9_2(X2,X1))
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_64,negated_conjecture,
    ( esk8_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | esk5_2(esk1_0,k1_tarski(esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_58])).

cnf(c_0_65,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_59])).

cnf(c_0_66,negated_conjecture,
    ( r3_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_60,c_0_18])).

cnf(c_0_67,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k1_tarski(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk9_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0))
    | r2_hidden(esk5_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_45,c_0_61])).

cnf(c_0_69,negated_conjecture,
    ( r2_hidden(esk8_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0))
    | r2_hidden(esk6_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_46])).

cnf(c_0_70,negated_conjecture,
    ( esk5_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | v2_waybel_0(k1_tarski(esk2_0),esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk9_2(esk1_0,k1_tarski(esk2_0)))
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r2_hidden(X1,k1_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_38]),c_0_26])])).

cnf(c_0_71,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_18]),c_0_26]),c_0_53])]),c_0_21])).

cnf(c_0_72,plain,
    ( r2_hidden(X1,k1_tarski(X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_67])])).

cnf(c_0_73,negated_conjecture,
    ( esk9_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | r2_hidden(esk5_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_68])).

cnf(c_0_74,negated_conjecture,
    ( esk8_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | r2_hidden(esk6_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_69])).

cnf(c_0_75,negated_conjecture,
    ( esk5_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | v2_waybel_0(k1_tarski(esk2_0),esk1_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk9_2(esk1_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_72])])).

cnf(c_0_76,negated_conjecture,
    ( esk9_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | esk5_2(esk1_0,k1_tarski(esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_73])).

cnf(c_0_77,negated_conjecture,
    ( esk8_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | esk6_2(esk1_0,k1_tarski(esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_74])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(esk9_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0))
    | r2_hidden(esk6_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_62,c_0_61])).

cnf(c_0_79,plain,
    ( v1_waybel_0(X3,X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r1_orders_2(X2,esk5_2(X2,X3),X1)
    | ~ r1_orders_2(X2,esk6_2(X2,X3),X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_80,negated_conjecture,
    ( esk5_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | v2_waybel_0(k1_tarski(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_71])])).

cnf(c_0_81,negated_conjecture,
    ( esk6_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | v2_waybel_0(k1_tarski(esk2_0),esk1_0)
    | ~ r1_orders_2(esk1_0,X1,esk9_2(esk1_0,k1_tarski(esk2_0)))
    | ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r2_hidden(X1,k1_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_77]),c_0_38]),c_0_26])])).

cnf(c_0_82,negated_conjecture,
    ( esk9_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | r2_hidden(esk6_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_78])).

cnf(c_0_83,plain,
    ( v1_waybel_0(X1,X2)
    | ~ r1_orders_2(X2,esk5_2(X2,X1),X3)
    | ~ r1_orders_2(X2,esk6_2(X2,X1),X3)
    | ~ r2_hidden(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(csr,[status(thm)],[c_0_79,c_0_57])).

cnf(c_0_84,negated_conjecture,
    ( esk5_2(esk1_0,k1_tarski(esk2_0)) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_45,c_0_80]),c_0_50])).

cnf(c_0_85,negated_conjecture,
    ( esk6_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | v2_waybel_0(k1_tarski(esk2_0),esk1_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk9_2(esk1_0,k1_tarski(esk2_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_71]),c_0_72])])).

cnf(c_0_86,negated_conjecture,
    ( esk9_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | esk6_2(esk1_0,k1_tarski(esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_82])).

cnf(c_0_87,negated_conjecture,
    ( v1_waybel_0(k1_tarski(esk2_0),esk1_0)
    | ~ r1_orders_2(esk1_0,esk6_2(esk1_0,k1_tarski(esk2_0)),X1)
    | ~ r1_orders_2(esk1_0,esk2_0,X1)
    | ~ r2_hidden(X1,k1_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_38]),c_0_26])])).

cnf(c_0_88,negated_conjecture,
    ( esk6_2(esk1_0,k1_tarski(esk2_0)) = esk2_0
    | v2_waybel_0(k1_tarski(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_86]),c_0_71])])).

cnf(c_0_89,negated_conjecture,
    ( v1_waybel_0(k1_tarski(esk2_0),esk1_0)
    | ~ r1_orders_2(esk1_0,esk6_2(esk1_0,k1_tarski(esk2_0)),esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_71]),c_0_72])])).

cnf(c_0_90,negated_conjecture,
    ( esk6_2(esk1_0,k1_tarski(esk2_0)) = esk2_0 ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_88]),c_0_50])).

cnf(c_0_91,negated_conjecture,
    ( v1_waybel_0(k1_tarski(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_89,c_0_90]),c_0_71])])).

cnf(c_0_92,negated_conjecture,
    ( ~ v2_waybel_0(k1_tarski(esk2_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_41,c_0_91])])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(esk8_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_46,c_0_92])).

cnf(c_0_94,negated_conjecture,
    ( r2_hidden(esk9_2(esk1_0,k1_tarski(esk2_0)),k1_tarski(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_61,c_0_92])).

cnf(c_0_95,negated_conjecture,
    ( esk8_2(esk1_0,k1_tarski(esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_93])).

cnf(c_0_96,negated_conjecture,
    ( esk9_2(esk1_0,k1_tarski(esk2_0)) = esk2_0 ),
    inference(spm,[status(thm)],[c_0_50,c_0_94])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,X1,esk2_0)
    | ~ r2_hidden(X1,k1_tarski(esk2_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_95]),c_0_38]),c_0_26])]),c_0_92]),c_0_96])])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_71]),c_0_72])]),
    [proof]).
%------------------------------------------------------------------------------
