%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:21:27 EST 2020

% Result     : Theorem 0.13s
% Output     : CNFRefutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 438 expanded)
%              Number of clauses        :   54 ( 172 expanded)
%              Number of leaves         :   16 ( 105 expanded)
%              Depth                    :   14
%              Number of atoms          :  307 (2961 expanded)
%              Number of equality atoms :   34 ( 122 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   28 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t8_waybel_7,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & v2_waybel_0(X2,X1)
            & v13_waybel_0(X2,X1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v1_subset_1(X2,u1_struct_0(X1))
          <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_waybel_7)).

fof(l3_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ! [X3] :
          ( r2_hidden(X3,X2)
         => r2_hidden(X3,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(t2_tarski,axiom,(
    ! [X1,X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X1)
        <=> r2_hidden(X3,X2) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(t34_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2,X3] :
          ( ( r1_tarski(X2,X3)
            & r1_yellow_0(X1,X2)
            & r1_yellow_0(X1,X3) )
         => r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_yellow_0)).

fof(t2_xboole_1,axiom,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(t34_waybel_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r1_yellow_0(X1,k5_waybel_0(X1,X2))
            & k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_waybel_0)).

fof(t42_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_yellow_0(X1)
        & l1_orders_2(X1) )
     => ( r1_yellow_0(X1,k1_xboole_0)
        & r2_yellow_0(X1,u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_yellow_0)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d20_waybel_0)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(d11_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_yellow_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(dt_k3_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_yellow_0(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & v2_waybel_0(X2,X1)
              & v13_waybel_0(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v1_subset_1(X2,u1_struct_0(X1))
            <=> ~ r2_hidden(k3_yellow_0(X1),X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t8_waybel_7])).

fof(c_0_17,plain,(
    ! [X11,X12,X13] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(X11))
      | ~ r2_hidden(X13,X12)
      | r2_hidden(X13,X11) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).

fof(c_0_18,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    & v3_orders_2(esk4_0)
    & v4_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & v1_yellow_0(esk4_0)
    & l1_orders_2(esk4_0)
    & ~ v1_xboole_0(esk5_0)
    & v2_waybel_0(esk5_0,esk4_0)
    & v13_waybel_0(esk5_0,esk4_0)
    & m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))
    & ( ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0))
      | r2_hidden(k3_yellow_0(esk4_0),esk5_0) )
    & ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
      | ~ r2_hidden(k3_yellow_0(esk4_0),esk5_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).

cnf(c_0_19,plain,
    ( r2_hidden(X3,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_20,negated_conjecture,
    ( m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_21,plain,(
    ! [X5,X6] :
      ( ( ~ r2_hidden(esk1_2(X5,X6),X5)
        | ~ r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 )
      & ( r2_hidden(esk1_2(X5,X6),X5)
        | r2_hidden(esk1_2(X5,X6),X6)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).

cnf(c_0_22,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk4_0))
    | ~ r2_hidden(X1,esk5_0) ),
    inference(spm,[status(thm)],[c_0_19,c_0_20])).

cnf(c_0_23,plain,
    ( r2_hidden(esk1_2(X1,X2),X1)
    | r2_hidden(esk1_2(X1,X2),X2)
    | X1 = X2 ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_24,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X14,X15)
      | m1_subset_1(X14,X15) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_25,negated_conjecture,
    ( esk5_0 = X1
    | r2_hidden(esk1_2(esk5_0,X1),u1_struct_0(esk4_0))
    | r2_hidden(esk1_2(esk5_0,X1),X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

fof(c_0_26,plain,(
    ! [X23,X24,X25] :
      ( ~ l1_orders_2(X23)
      | ~ r1_tarski(X24,X25)
      | ~ r1_yellow_0(X23,X24)
      | ~ r1_yellow_0(X23,X25)
      | r1_orders_2(X23,k1_yellow_0(X23,X24),k1_yellow_0(X23,X25)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).

fof(c_0_27,plain,(
    ! [X8] : r1_tarski(k1_xboole_0,X8) ),
    inference(variable_rename,[status(thm)],[t2_xboole_1])).

fof(c_0_28,plain,(
    ! [X33,X34] :
      ( ( r1_yellow_0(X33,k5_waybel_0(X33,X34))
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ l1_orders_2(X33) )
      & ( k1_yellow_0(X33,k5_waybel_0(X33,X34)) = X34
        | ~ m1_subset_1(X34,u1_struct_0(X33))
        | v2_struct_0(X33)
        | ~ v3_orders_2(X33)
        | ~ v4_orders_2(X33)
        | ~ v5_orders_2(X33)
        | ~ l1_orders_2(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).

cnf(c_0_29,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_30,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0)
    | r2_hidden(esk1_2(esk5_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(ef,[status(thm)],[c_0_25])).

fof(c_0_31,plain,(
    ! [X26] :
      ( ( r1_yellow_0(X26,k1_xboole_0)
        | v2_struct_0(X26)
        | ~ v5_orders_2(X26)
        | ~ v1_yellow_0(X26)
        | ~ l1_orders_2(X26) )
      & ( r2_yellow_0(X26,u1_struct_0(X26))
        | v2_struct_0(X26)
        | ~ v5_orders_2(X26)
        | ~ v1_yellow_0(X26)
        | ~ l1_orders_2(X26) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).

cnf(c_0_32,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ r1_tarski(X2,X3)
    | ~ r1_yellow_0(X1,X2)
    | ~ r1_yellow_0(X1,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( r1_tarski(k1_xboole_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_34,plain,
    ( r1_yellow_0(X1,k5_waybel_0(X1,X2))
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0)
    | m1_subset_1(esk1_2(esk5_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_36,negated_conjecture,
    ( v4_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_37,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_38,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_39,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_40,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_41,plain,
    ( r1_yellow_0(X1,k1_xboole_0)
    | v2_struct_0(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_yellow_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_42,negated_conjecture,
    ( v1_yellow_0(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_43,plain,(
    ! [X35,X36] :
      ( ( ~ v1_subset_1(X36,X35)
        | X36 != X35
        | ~ m1_subset_1(X36,k1_zfmisc_1(X35)) )
      & ( X36 = X35
        | v1_subset_1(X36,X35)
        | ~ m1_subset_1(X36,k1_zfmisc_1(X35)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_44,plain,
    ( r1_orders_2(X1,k1_yellow_0(X1,k1_xboole_0),k1_yellow_0(X1,X2))
    | ~ r1_yellow_0(X1,k1_xboole_0)
    | ~ r1_yellow_0(X1,X2)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_45,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0)
    | r1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0)))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_46,negated_conjecture,
    ( r1_yellow_0(esk4_0,k1_xboole_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41,c_0_42]),c_0_38]),c_0_39])]),c_0_40])).

cnf(c_0_47,plain,
    ( k1_yellow_0(X1,k5_waybel_0(X1,X2)) = X2
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_48,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

fof(c_0_49,plain,(
    ! [X27,X28,X29,X30] :
      ( ( ~ v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X29,u1_struct_0(X27))
        | ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r2_hidden(X29,X28)
        | ~ r1_orders_2(X27,X29,X30)
        | r2_hidden(X30,X28)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) )
      & ( m1_subset_1(esk2_2(X27,X28),u1_struct_0(X27))
        | v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) )
      & ( m1_subset_1(esk3_2(X27,X28),u1_struct_0(X27))
        | v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) )
      & ( r2_hidden(esk2_2(X27,X28),X28)
        | v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) )
      & ( r1_orders_2(X27,esk2_2(X27,X28),esk3_2(X27,X28))
        | v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) )
      & ( ~ r2_hidden(esk3_2(X27,X28),X28)
        | v13_waybel_0(X28,X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))
        | ~ l1_orders_2(X27) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).

fof(c_0_50,plain,(
    ! [X18,X19,X20] :
      ( ~ r2_hidden(X18,X19)
      | ~ m1_subset_1(X19,k1_zfmisc_1(X20))
      | m1_subset_1(X18,X20) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_51,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0)
    | r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0))))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_45]),c_0_46]),c_0_39])])).

cnf(c_0_52,negated_conjecture,
    ( k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0)))) = esk1_2(esk5_0,u1_struct_0(esk4_0))
    | esk5_0 = u1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_35]),c_0_36]),c_0_37]),c_0_38]),c_0_39])]),c_0_40])).

fof(c_0_53,plain,(
    ! [X21] :
      ( ~ l1_orders_2(X21)
      | k3_yellow_0(X21) = k1_yellow_0(X21,k1_xboole_0) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk4_0),esk5_0)
    | ~ v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_55,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0)
    | v1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_48,c_0_20])).

cnf(c_0_56,plain,
    ( r2_hidden(X4,X1)
    | ~ v13_waybel_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,X1)
    | ~ r1_orders_2(X2,X3,X4)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_57,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0)
    | r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),esk1_2(esk5_0,u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,plain,
    ( k3_yellow_0(X1) = k1_yellow_0(X1,k1_xboole_0)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_60,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0)
    | r2_hidden(k3_yellow_0(esk4_0),esk5_0) ),
    inference(spm,[status(thm)],[c_0_54,c_0_55])).

fof(c_0_61,plain,(
    ! [X16,X17] :
      ( ~ m1_subset_1(X16,X17)
      | v1_xboole_0(X17)
      | r2_hidden(X16,X17) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_62,plain,(
    ! [X22] :
      ( ~ l1_orders_2(X22)
      | m1_subset_1(k3_yellow_0(X22),u1_struct_0(X22)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).

fof(c_0_63,plain,(
    ! [X10] : m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_64,plain,(
    ! [X9] : k2_subset_1(X9) = X9 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,X2)
    | ~ v13_waybel_0(X2,X3)
    | ~ r1_orders_2(X3,X4,X1)
    | ~ l1_orders_2(X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ r2_hidden(X4,X2) ),
    inference(csr,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0)
    | r1_orders_2(esk4_0,k3_yellow_0(esk4_0),esk1_2(esk5_0,u1_struct_0(esk4_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_39])])).

cnf(c_0_67,plain,
    ( X1 = X2
    | ~ r2_hidden(esk1_2(X1,X2),X1)
    | ~ r2_hidden(esk1_2(X1,X2),X2) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_68,negated_conjecture,
    ( ~ v1_xboole_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_69,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0)
    | r2_hidden(k3_yellow_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_60])).

cnf(c_0_70,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_61])).

cnf(c_0_71,plain,
    ( m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_72,plain,
    ( ~ v1_subset_1(X1,X2)
    | X1 != X2
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_73,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_63])).

cnf(c_0_74,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_75,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0)
    | r2_hidden(esk1_2(esk5_0,u1_struct_0(esk4_0)),X1)
    | ~ v13_waybel_0(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(k3_yellow_0(esk4_0),X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_66]),c_0_39])]),c_0_35])).

cnf(c_0_76,negated_conjecture,
    ( v13_waybel_0(esk5_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_77,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0)
    | ~ r2_hidden(esk1_2(esk5_0,u1_struct_0(esk4_0)),esk5_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_30])).

cnf(c_0_78,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk4_0),u1_struct_0(esk4_0))
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_79,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_hidden(k3_yellow_0(X1),u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_80,plain,
    ( ~ v1_subset_1(X1,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(er,[status(thm)],[c_0_72])).

cnf(c_0_81,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_73,c_0_74])).

cnf(c_0_82,negated_conjecture,
    ( v1_subset_1(esk5_0,u1_struct_0(esk4_0))
    | ~ r2_hidden(k3_yellow_0(esk4_0),esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_83,negated_conjecture,
    ( esk5_0 = u1_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_20]),c_0_76])]),c_0_60]),c_0_77])).

cnf(c_0_84,negated_conjecture,
    ( r2_hidden(k3_yellow_0(esk4_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_39])])).

cnf(c_0_85,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80,c_0_81])])).

cnf(c_0_86,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82,c_0_83]),c_0_83]),c_0_84])]),c_0_85]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:30:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.13/0.40  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S2q
% 0.13/0.40  # and selection function SelectCQArNTNp.
% 0.13/0.40  #
% 0.13/0.40  # Preprocessing time       : 0.046 s
% 0.13/0.40  # Presaturation interreduction done
% 0.13/0.40  
% 0.13/0.40  # Proof found!
% 0.13/0.40  # SZS status Theorem
% 0.13/0.40  # SZS output start CNFRefutation
% 0.13/0.40  fof(t8_waybel_7, conjecture, ![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_waybel_7)).
% 0.13/0.40  fof(l3_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(X3,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 0.13/0.40  fof(t2_tarski, axiom, ![X1, X2]:(![X3]:(r2_hidden(X3,X1)<=>r2_hidden(X3,X2))=>X1=X2), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 0.13/0.40  fof(t1_subset, axiom, ![X1, X2]:(r2_hidden(X1,X2)=>m1_subset_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 0.13/0.40  fof(t34_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2, X3]:(((r1_tarski(X2,X3)&r1_yellow_0(X1,X2))&r1_yellow_0(X1,X3))=>r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_yellow_0)).
% 0.13/0.40  fof(t2_xboole_1, axiom, ![X1]:r1_tarski(k1_xboole_0,X1), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 0.13/0.40  fof(t34_waybel_0, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>(r1_yellow_0(X1,k5_waybel_0(X1,X2))&k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_waybel_0)).
% 0.13/0.40  fof(t42_yellow_0, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>(r1_yellow_0(X1,k1_xboole_0)&r2_yellow_0(X1,u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_yellow_0)).
% 0.13/0.40  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.13/0.40  fof(d20_waybel_0, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>(v13_waybel_0(X2,X1)<=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>((r2_hidden(X3,X2)&r1_orders_2(X1,X3,X4))=>r2_hidden(X4,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d20_waybel_0)).
% 0.13/0.40  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 0.13/0.40  fof(d11_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d11_yellow_0)).
% 0.13/0.40  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.13/0.40  fof(dt_k3_yellow_0, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_yellow_0)).
% 0.13/0.40  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.13/0.40  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.13/0.40  fof(c_0_16, negated_conjecture, ~(![X1]:((((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&v1_yellow_0(X1))&l1_orders_2(X1))=>![X2]:((((~(v1_xboole_0(X2))&v2_waybel_0(X2,X1))&v13_waybel_0(X2,X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_subset_1(X2,u1_struct_0(X1))<=>~(r2_hidden(k3_yellow_0(X1),X2)))))), inference(assume_negation,[status(cth)],[t8_waybel_7])).
% 0.13/0.40  fof(c_0_17, plain, ![X11, X12, X13]:(~m1_subset_1(X12,k1_zfmisc_1(X11))|(~r2_hidden(X13,X12)|r2_hidden(X13,X11))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[l3_subset_1])])])).
% 0.13/0.40  fof(c_0_18, negated_conjecture, ((((((~v2_struct_0(esk4_0)&v3_orders_2(esk4_0))&v4_orders_2(esk4_0))&v5_orders_2(esk4_0))&v1_yellow_0(esk4_0))&l1_orders_2(esk4_0))&((((~v1_xboole_0(esk5_0)&v2_waybel_0(esk5_0,esk4_0))&v13_waybel_0(esk5_0,esk4_0))&m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0))))&((~v1_subset_1(esk5_0,u1_struct_0(esk4_0))|r2_hidden(k3_yellow_0(esk4_0),esk5_0))&(v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~r2_hidden(k3_yellow_0(esk4_0),esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])).
% 0.13/0.40  cnf(c_0_19, plain, (r2_hidden(X3,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.13/0.40  cnf(c_0_20, negated_conjecture, (m1_subset_1(esk5_0,k1_zfmisc_1(u1_struct_0(esk4_0)))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  fof(c_0_21, plain, ![X5, X6]:((~r2_hidden(esk1_2(X5,X6),X5)|~r2_hidden(esk1_2(X5,X6),X6)|X5=X6)&(r2_hidden(esk1_2(X5,X6),X5)|r2_hidden(esk1_2(X5,X6),X6)|X5=X6)), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_tarski])])])])).
% 0.13/0.40  cnf(c_0_22, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk4_0))|~r2_hidden(X1,esk5_0)), inference(spm,[status(thm)],[c_0_19, c_0_20])).
% 0.13/0.40  cnf(c_0_23, plain, (r2_hidden(esk1_2(X1,X2),X1)|r2_hidden(esk1_2(X1,X2),X2)|X1=X2), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  fof(c_0_24, plain, ![X14, X15]:(~r2_hidden(X14,X15)|m1_subset_1(X14,X15)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).
% 0.13/0.40  cnf(c_0_25, negated_conjecture, (esk5_0=X1|r2_hidden(esk1_2(esk5_0,X1),u1_struct_0(esk4_0))|r2_hidden(esk1_2(esk5_0,X1),X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.13/0.40  fof(c_0_26, plain, ![X23, X24, X25]:(~l1_orders_2(X23)|(~r1_tarski(X24,X25)|~r1_yellow_0(X23,X24)|~r1_yellow_0(X23,X25)|r1_orders_2(X23,k1_yellow_0(X23,X24),k1_yellow_0(X23,X25)))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t34_yellow_0])])])).
% 0.13/0.40  fof(c_0_27, plain, ![X8]:r1_tarski(k1_xboole_0,X8), inference(variable_rename,[status(thm)],[t2_xboole_1])).
% 0.13/0.40  fof(c_0_28, plain, ![X33, X34]:((r1_yellow_0(X33,k5_waybel_0(X33,X34))|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33)))&(k1_yellow_0(X33,k5_waybel_0(X33,X34))=X34|~m1_subset_1(X34,u1_struct_0(X33))|(v2_struct_0(X33)|~v3_orders_2(X33)|~v4_orders_2(X33)|~v5_orders_2(X33)|~l1_orders_2(X33)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t34_waybel_0])])])])])).
% 0.13/0.40  cnf(c_0_29, plain, (m1_subset_1(X1,X2)|~r2_hidden(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_24])).
% 0.13/0.40  cnf(c_0_30, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)|r2_hidden(esk1_2(esk5_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(ef,[status(thm)],[c_0_25])).
% 0.13/0.40  fof(c_0_31, plain, ![X26]:((r1_yellow_0(X26,k1_xboole_0)|(v2_struct_0(X26)|~v5_orders_2(X26)|~v1_yellow_0(X26)|~l1_orders_2(X26)))&(r2_yellow_0(X26,u1_struct_0(X26))|(v2_struct_0(X26)|~v5_orders_2(X26)|~v1_yellow_0(X26)|~l1_orders_2(X26)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t42_yellow_0])])])])).
% 0.13/0.40  cnf(c_0_32, plain, (r1_orders_2(X1,k1_yellow_0(X1,X2),k1_yellow_0(X1,X3))|~l1_orders_2(X1)|~r1_tarski(X2,X3)|~r1_yellow_0(X1,X2)|~r1_yellow_0(X1,X3)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.13/0.40  cnf(c_0_33, plain, (r1_tarski(k1_xboole_0,X1)), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.13/0.40  cnf(c_0_34, plain, (r1_yellow_0(X1,k5_waybel_0(X1,X2))|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.40  cnf(c_0_35, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)|m1_subset_1(esk1_2(esk5_0,u1_struct_0(esk4_0)),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.13/0.40  cnf(c_0_36, negated_conjecture, (v4_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_37, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_38, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_39, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_40, negated_conjecture, (~v2_struct_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_41, plain, (r1_yellow_0(X1,k1_xboole_0)|v2_struct_0(X1)|~v5_orders_2(X1)|~v1_yellow_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_31])).
% 0.13/0.40  cnf(c_0_42, negated_conjecture, (v1_yellow_0(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  fof(c_0_43, plain, ![X35, X36]:((~v1_subset_1(X36,X35)|X36!=X35|~m1_subset_1(X36,k1_zfmisc_1(X35)))&(X36=X35|v1_subset_1(X36,X35)|~m1_subset_1(X36,k1_zfmisc_1(X35)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.13/0.40  cnf(c_0_44, plain, (r1_orders_2(X1,k1_yellow_0(X1,k1_xboole_0),k1_yellow_0(X1,X2))|~r1_yellow_0(X1,k1_xboole_0)|~r1_yellow_0(X1,X2)|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.13/0.40  cnf(c_0_45, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)|r1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])]), c_0_40])).
% 0.13/0.40  cnf(c_0_46, negated_conjecture, (r1_yellow_0(esk4_0,k1_xboole_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_41, c_0_42]), c_0_38]), c_0_39])]), c_0_40])).
% 0.13/0.40  cnf(c_0_47, plain, (k1_yellow_0(X1,k5_waybel_0(X1,X2))=X2|v2_struct_0(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.13/0.40  cnf(c_0_48, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.40  fof(c_0_49, plain, ![X27, X28, X29, X30]:((~v13_waybel_0(X28,X27)|(~m1_subset_1(X29,u1_struct_0(X27))|(~m1_subset_1(X30,u1_struct_0(X27))|(~r2_hidden(X29,X28)|~r1_orders_2(X27,X29,X30)|r2_hidden(X30,X28))))|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27))&((m1_subset_1(esk2_2(X27,X28),u1_struct_0(X27))|v13_waybel_0(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27))&((m1_subset_1(esk3_2(X27,X28),u1_struct_0(X27))|v13_waybel_0(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27))&(((r2_hidden(esk2_2(X27,X28),X28)|v13_waybel_0(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27))&(r1_orders_2(X27,esk2_2(X27,X28),esk3_2(X27,X28))|v13_waybel_0(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27)))&(~r2_hidden(esk3_2(X27,X28),X28)|v13_waybel_0(X28,X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))|~l1_orders_2(X27)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d20_waybel_0])])])])])).
% 0.13/0.40  fof(c_0_50, plain, ![X18, X19, X20]:(~r2_hidden(X18,X19)|~m1_subset_1(X19,k1_zfmisc_1(X20))|m1_subset_1(X18,X20)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.13/0.40  cnf(c_0_51, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)|r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0)))))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_44, c_0_45]), c_0_46]), c_0_39])])).
% 0.13/0.40  cnf(c_0_52, negated_conjecture, (k1_yellow_0(esk4_0,k5_waybel_0(esk4_0,esk1_2(esk5_0,u1_struct_0(esk4_0))))=esk1_2(esk5_0,u1_struct_0(esk4_0))|esk5_0=u1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_35]), c_0_36]), c_0_37]), c_0_38]), c_0_39])]), c_0_40])).
% 0.13/0.40  fof(c_0_53, plain, ![X21]:(~l1_orders_2(X21)|k3_yellow_0(X21)=k1_yellow_0(X21,k1_xboole_0)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_yellow_0])])).
% 0.13/0.40  cnf(c_0_54, negated_conjecture, (r2_hidden(k3_yellow_0(esk4_0),esk5_0)|~v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_55, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)|v1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_48, c_0_20])).
% 0.13/0.40  cnf(c_0_56, plain, (r2_hidden(X4,X1)|~v13_waybel_0(X1,X2)|~m1_subset_1(X3,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~r2_hidden(X3,X1)|~r1_orders_2(X2,X3,X4)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.13/0.40  cnf(c_0_57, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.13/0.40  cnf(c_0_58, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)|r1_orders_2(esk4_0,k1_yellow_0(esk4_0,k1_xboole_0),esk1_2(esk5_0,u1_struct_0(esk4_0)))), inference(spm,[status(thm)],[c_0_51, c_0_52])).
% 0.13/0.40  cnf(c_0_59, plain, (k3_yellow_0(X1)=k1_yellow_0(X1,k1_xboole_0)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_53])).
% 0.13/0.40  cnf(c_0_60, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)|r2_hidden(k3_yellow_0(esk4_0),esk5_0)), inference(spm,[status(thm)],[c_0_54, c_0_55])).
% 0.13/0.40  fof(c_0_61, plain, ![X16, X17]:(~m1_subset_1(X16,X17)|(v1_xboole_0(X17)|r2_hidden(X16,X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.13/0.40  fof(c_0_62, plain, ![X22]:(~l1_orders_2(X22)|m1_subset_1(k3_yellow_0(X22),u1_struct_0(X22))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k3_yellow_0])])).
% 0.13/0.40  fof(c_0_63, plain, ![X10]:m1_subset_1(k2_subset_1(X10),k1_zfmisc_1(X10)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.13/0.40  fof(c_0_64, plain, ![X9]:k2_subset_1(X9)=X9, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.13/0.40  cnf(c_0_65, plain, (r2_hidden(X1,X2)|~v13_waybel_0(X2,X3)|~r1_orders_2(X3,X4,X1)|~l1_orders_2(X3)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X3)))|~m1_subset_1(X1,u1_struct_0(X3))|~r2_hidden(X4,X2)), inference(csr,[status(thm)],[c_0_56, c_0_57])).
% 0.13/0.40  cnf(c_0_66, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)|r1_orders_2(esk4_0,k3_yellow_0(esk4_0),esk1_2(esk5_0,u1_struct_0(esk4_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_59]), c_0_39])])).
% 0.13/0.40  cnf(c_0_67, plain, (X1=X2|~r2_hidden(esk1_2(X1,X2),X1)|~r2_hidden(esk1_2(X1,X2),X2)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.13/0.40  cnf(c_0_68, negated_conjecture, (~v1_xboole_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_69, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)|r2_hidden(k3_yellow_0(esk4_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_22, c_0_60])).
% 0.13/0.40  cnf(c_0_70, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_61])).
% 0.13/0.40  cnf(c_0_71, plain, (m1_subset_1(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_62])).
% 0.13/0.40  cnf(c_0_72, plain, (~v1_subset_1(X1,X2)|X1!=X2|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.13/0.40  cnf(c_0_73, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_63])).
% 0.13/0.40  cnf(c_0_74, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_64])).
% 0.13/0.40  cnf(c_0_75, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)|r2_hidden(esk1_2(esk5_0,u1_struct_0(esk4_0)),X1)|~v13_waybel_0(X1,esk4_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))|~r2_hidden(k3_yellow_0(esk4_0),X1)), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_66]), c_0_39])]), c_0_35])).
% 0.13/0.40  cnf(c_0_76, negated_conjecture, (v13_waybel_0(esk5_0,esk4_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_77, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)|~r2_hidden(esk1_2(esk5_0,u1_struct_0(esk4_0)),esk5_0)), inference(spm,[status(thm)],[c_0_67, c_0_30])).
% 0.13/0.40  cnf(c_0_78, negated_conjecture, (r2_hidden(k3_yellow_0(esk4_0),u1_struct_0(esk4_0))|~v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.13/0.40  cnf(c_0_79, plain, (v1_xboole_0(u1_struct_0(X1))|r2_hidden(k3_yellow_0(X1),u1_struct_0(X1))|~l1_orders_2(X1)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.13/0.40  cnf(c_0_80, plain, (~v1_subset_1(X1,X1)|~m1_subset_1(X1,k1_zfmisc_1(X1))), inference(er,[status(thm)],[c_0_72])).
% 0.13/0.40  cnf(c_0_81, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_73, c_0_74])).
% 0.13/0.40  cnf(c_0_82, negated_conjecture, (v1_subset_1(esk5_0,u1_struct_0(esk4_0))|~r2_hidden(k3_yellow_0(esk4_0),esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.13/0.40  cnf(c_0_83, negated_conjecture, (esk5_0=u1_struct_0(esk4_0)), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_20]), c_0_76])]), c_0_60]), c_0_77])).
% 0.13/0.40  cnf(c_0_84, negated_conjecture, (r2_hidden(k3_yellow_0(esk4_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_79]), c_0_39])])).
% 0.13/0.40  cnf(c_0_85, plain, (~v1_subset_1(X1,X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_80, c_0_81])])).
% 0.13/0.40  cnf(c_0_86, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_82, c_0_83]), c_0_83]), c_0_84])]), c_0_85]), ['proof']).
% 0.13/0.40  # SZS output end CNFRefutation
% 0.13/0.40  # Proof object total steps             : 87
% 0.13/0.40  # Proof object clause steps            : 54
% 0.13/0.40  # Proof object formula steps           : 33
% 0.13/0.40  # Proof object conjectures             : 33
% 0.13/0.40  # Proof object clause conjectures      : 30
% 0.13/0.40  # Proof object formula conjectures     : 3
% 0.13/0.40  # Proof object initial clauses used    : 29
% 0.13/0.40  # Proof object initial formulas used   : 16
% 0.13/0.40  # Proof object generating inferences   : 20
% 0.13/0.40  # Proof object simplifying inferences  : 40
% 0.13/0.40  # Training examples: 0 positive, 0 negative
% 0.13/0.40  # Parsed axioms                        : 16
% 0.13/0.40  # Removed by relevancy pruning/SinE    : 0
% 0.13/0.40  # Initial clauses                      : 36
% 0.13/0.40  # Removed in clause preprocessing      : 1
% 0.13/0.40  # Initial clauses in saturation        : 35
% 0.13/0.40  # Processed clauses                    : 152
% 0.13/0.40  # ...of these trivial                  : 0
% 0.13/0.40  # ...subsumed                          : 19
% 0.13/0.40  # ...remaining for further processing  : 133
% 0.13/0.40  # Other redundant clauses eliminated   : 1
% 0.13/0.40  # Clauses deleted for lack of memory   : 0
% 0.13/0.40  # Backward-subsumed                    : 4
% 0.13/0.40  # Backward-rewritten                   : 39
% 0.13/0.40  # Generated clauses                    : 160
% 0.13/0.40  # ...of the previous two non-trivial   : 143
% 0.13/0.40  # Contextual simplify-reflections      : 4
% 0.13/0.40  # Paramodulations                      : 151
% 0.13/0.40  # Factorizations                       : 8
% 0.13/0.40  # Equation resolutions                 : 1
% 0.13/0.40  # Propositional unsat checks           : 0
% 0.13/0.40  #    Propositional check models        : 0
% 0.13/0.40  #    Propositional check unsatisfiable : 0
% 0.13/0.40  #    Propositional clauses             : 0
% 0.13/0.40  #    Propositional clauses after purity: 0
% 0.13/0.40  #    Propositional unsat core size     : 0
% 0.13/0.40  #    Propositional preprocessing time  : 0.000
% 0.13/0.40  #    Propositional encoding time       : 0.000
% 0.13/0.40  #    Propositional solver time         : 0.000
% 0.13/0.40  #    Success case prop preproc time    : 0.000
% 0.13/0.40  #    Success case prop encoding time   : 0.000
% 0.13/0.40  #    Success case prop solver time     : 0.000
% 0.13/0.40  # Current number of processed clauses  : 54
% 0.13/0.40  #    Positive orientable unit clauses  : 16
% 0.13/0.40  #    Positive unorientable unit clauses: 0
% 0.13/0.40  #    Negative unit clauses             : 2
% 0.13/0.40  #    Non-unit-clauses                  : 36
% 0.13/0.40  # Current number of unprocessed clauses: 47
% 0.13/0.40  # ...number of literals in the above   : 225
% 0.13/0.40  # Current number of archived formulas  : 0
% 0.13/0.40  # Current number of archived clauses   : 79
% 0.13/0.40  # Clause-clause subsumption calls (NU) : 501
% 0.13/0.40  # Rec. Clause-clause subsumption calls : 173
% 0.13/0.40  # Non-unit clause-clause subsumptions  : 22
% 0.13/0.40  # Unit Clause-clause subsumption calls : 16
% 0.13/0.40  # Rewrite failures with RHS unbound    : 0
% 0.13/0.40  # BW rewrite match attempts            : 9
% 0.13/0.40  # BW rewrite match successes           : 6
% 0.13/0.40  # Condensation attempts                : 0
% 0.13/0.40  # Condensation successes               : 0
% 0.13/0.40  # Termbank termtop insertions          : 6021
% 0.13/0.41  
% 0.13/0.41  # -------------------------------------------------
% 0.13/0.41  # User time                : 0.061 s
% 0.13/0.41  # System time              : 0.004 s
% 0.13/0.41  # Total time               : 0.065 s
% 0.13/0.41  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
