%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : orders_2__t38_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:20 EDT 2019

% Result     : Theorem 277.12s
% Output     : CNFRefutation 277.12s
% Verified   : 
% Statistics : Number of formulae       :  151 (6925 expanded)
%              Number of clauses        :  103 (2821 expanded)
%              Number of leaves         :   24 (1794 expanded)
%              Depth                    :   26
%              Number of atoms          :  620 (73147 expanded)
%              Number of equality atoms :   32 (1045 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal clause size      :   52 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t38_orders_2,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ~ ( ? [X4] :
                        ( v6_orders_2(X4,X1)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X2,X4)
                        & r2_hidden(X3,X4) )
                    & ~ r1_orders_2(X1,X2,X3)
                    & ~ r1_orders_2(X1,X3,X2) )
                & ~ ( ( r1_orders_2(X1,X2,X3)
                      | r1_orders_2(X1,X3,X2) )
                    & ! [X4] :
                        ( ( v6_orders_2(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                       => ~ ( r2_hidden(X2,X4)
                            & r2_hidden(X3,X4) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',t38_orders_2)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',t7_boole)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',d9_orders_2)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',t3_subset)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',t5_subset)).

fof(t8_boole,axiom,(
    ! [X1,X2] :
      ~ ( v1_xboole_0(X1)
        & X1 != X2
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',t8_boole)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',cc4_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',dt_u1_orders_2)).

fof(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',dt_o_0_0_xboole_0)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',fc1_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',dt_l1_orders_2)).

fof(reflexivity_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => r3_orders_2(X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',reflexivity_r3_orders_2)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',redefinition_r3_orders_2)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',existence_m1_subset_1)).

fof(dt_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',dt_k7_domain_1)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',redefinition_k7_domain_1)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',d2_tarski)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',commutativity_k2_tarski)).

fof(t36_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ( v6_orders_2(k7_domain_1(u1_struct_0(X1),X2,X3),X1)
                  & m1_subset_1(k7_domain_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(X1))) )
              <=> ( r3_orders_2(X1,X2,X3)
                  | r3_orders_2(X1,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',t36_orders_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',t2_subset)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',t1_subset)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',d11_orders_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',cc1_relset_1)).

fof(d7_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r7_relat_2(X1,X2)
        <=> ! [X3,X4] :
              ~ ( r2_hidden(X3,X2)
                & r2_hidden(X4,X2)
                & ~ r2_hidden(k4_tarski(X3,X4),X1)
                & ~ r2_hidden(k4_tarski(X4,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t38_orders_2.p',d7_relat_2)).

fof(c_0_24,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( ~ ( ? [X4] :
                          ( v6_orders_2(X4,X1)
                          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                          & r2_hidden(X2,X4)
                          & r2_hidden(X3,X4) )
                      & ~ r1_orders_2(X1,X2,X3)
                      & ~ r1_orders_2(X1,X3,X2) )
                  & ~ ( ( r1_orders_2(X1,X2,X3)
                        | r1_orders_2(X1,X3,X2) )
                      & ! [X4] :
                          ( ( v6_orders_2(X4,X1)
                            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                         => ~ ( r2_hidden(X2,X4)
                              & r2_hidden(X3,X4) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t38_orders_2])).

fof(c_0_25,plain,(
    ! [X72,X73] :
      ( ~ r2_hidden(X72,X73)
      | ~ v1_xboole_0(X73) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_26,plain,(
    ! [X35,X36,X37] :
      ( ( ~ r1_orders_2(X35,X36,X37)
        | r2_hidden(k4_tarski(X36,X37),u1_orders_2(X35))
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ l1_orders_2(X35) )
      & ( ~ r2_hidden(k4_tarski(X36,X37),u1_orders_2(X35))
        | r1_orders_2(X35,X36,X37)
        | ~ m1_subset_1(X37,u1_struct_0(X35))
        | ~ m1_subset_1(X36,u1_struct_0(X35))
        | ~ l1_orders_2(X35) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

fof(c_0_27,plain,(
    ! [X63,X64] :
      ( ( ~ m1_subset_1(X63,k1_zfmisc_1(X64))
        | r1_tarski(X63,X64) )
      & ( ~ r1_tarski(X63,X64)
        | m1_subset_1(X63,k1_zfmisc_1(X64)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

fof(c_0_28,negated_conjecture,(
    ! [X9] :
      ( v3_orders_2(esk1_0)
      & l1_orders_2(esk1_0)
      & m1_subset_1(esk2_0,u1_struct_0(esk1_0))
      & m1_subset_1(esk3_0,u1_struct_0(esk1_0))
      & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
        | r1_orders_2(esk1_0,esk3_0,esk2_0)
        | v6_orders_2(esk4_0,esk1_0) )
      & ( ~ v6_orders_2(X9,esk1_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r2_hidden(esk2_0,X9)
        | ~ r2_hidden(esk3_0,X9)
        | v6_orders_2(esk4_0,esk1_0) )
      & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
        | r1_orders_2(esk1_0,esk3_0,esk2_0)
        | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
      & ( ~ v6_orders_2(X9,esk1_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r2_hidden(esk2_0,X9)
        | ~ r2_hidden(esk3_0,X9)
        | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) )
      & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
        | r1_orders_2(esk1_0,esk3_0,esk2_0)
        | r2_hidden(esk2_0,esk4_0) )
      & ( ~ v6_orders_2(X9,esk1_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r2_hidden(esk2_0,X9)
        | ~ r2_hidden(esk3_0,X9)
        | r2_hidden(esk2_0,esk4_0) )
      & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
        | r1_orders_2(esk1_0,esk3_0,esk2_0)
        | r2_hidden(esk3_0,esk4_0) )
      & ( ~ v6_orders_2(X9,esk1_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r2_hidden(esk2_0,X9)
        | ~ r2_hidden(esk3_0,X9)
        | r2_hidden(esk3_0,esk4_0) )
      & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
        | r1_orders_2(esk1_0,esk3_0,esk2_0)
        | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) )
      & ( ~ v6_orders_2(X9,esk1_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r2_hidden(esk2_0,X9)
        | ~ r2_hidden(esk3_0,X9)
        | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) )
      & ( r1_orders_2(esk1_0,esk2_0,esk3_0)
        | r1_orders_2(esk1_0,esk3_0,esk2_0)
        | ~ r1_orders_2(esk1_0,esk3_0,esk2_0) )
      & ( ~ v6_orders_2(X9,esk1_0)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(esk1_0)))
        | ~ r2_hidden(esk2_0,X9)
        | ~ r2_hidden(esk3_0,X9)
        | ~ r1_orders_2(esk1_0,esk3_0,esk2_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_24])])])])])])).

cnf(c_0_29,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_30,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_31,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_32,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | m1_subset_1(esk4_0,k1_zfmisc_1(u1_struct_0(esk1_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_33,plain,(
    ! [X68,X69,X70] :
      ( ~ r2_hidden(X68,X69)
      | ~ m1_subset_1(X69,k1_zfmisc_1(X70))
      | ~ v1_xboole_0(X70) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_34,plain,
    ( ~ v1_xboole_0(u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_35,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk1_0))
    | r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(spm,[status(thm)],[c_0_31,c_0_32])).

cnf(c_0_36,negated_conjecture,
    ( m1_subset_1(esk2_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_37,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

fof(c_0_39,plain,(
    ! [X74,X75] :
      ( ~ v1_xboole_0(X74)
      | X74 = X75
      | ~ v1_xboole_0(X75) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t8_boole])])).

fof(c_0_40,plain,(
    ! [X80,X81,X82] :
      ( ~ v1_xboole_0(X80)
      | ~ m1_subset_1(X82,k1_zfmisc_1(k2_zfmisc_1(X81,X80)))
      | v1_xboole_0(X82) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_41,plain,(
    ! [X42] :
      ( ~ l1_orders_2(X42)
      | m1_subset_1(u1_orders_2(X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X42),u1_struct_0(X42)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

cnf(c_0_42,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_43,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_44,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk1_0))
    | r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ v1_xboole_0(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_35]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_45,plain,
    ( X1 = X2
    | ~ v1_xboole_0(X1)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_46,plain,
    ( v1_xboole_0(o_0_0_xboole_0) ),
    inference(split_conjunct,[status(thm)],[dt_o_0_0_xboole_0])).

cnf(c_0_47,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

fof(c_0_49,plain,(
    ! [X83] :
      ( ~ v2_struct_0(X83)
      | ~ l1_struct_0(X83)
      | v1_xboole_0(u1_struct_0(X83)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

cnf(c_0_50,plain,
    ( ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2)
    | ~ r2_hidden(X3,X1) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk1_0))
    | ~ v1_xboole_0(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_44]),c_0_37]),c_0_36]),c_0_38])])).

cnf(c_0_52,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_53,plain,
    ( X1 = o_0_0_xboole_0
    | ~ v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_54,plain,
    ( v1_xboole_0(u1_orders_2(X1))
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_47,c_0_48])).

cnf(c_0_55,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

fof(c_0_56,plain,(
    ! [X41] :
      ( ~ l1_orders_2(X41)
      | l1_struct_0(X41) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_57,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0))
    | ~ v1_xboole_0(u1_orders_2(esk1_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_58,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_hidden(esk3_0,esk4_0)
    | ~ v1_xboole_0(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_52]),c_0_36]),c_0_37]),c_0_38])])).

cnf(c_0_59,plain,
    ( u1_orders_2(X1) = o_0_0_xboole_0
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_60,plain,
    ( u1_struct_0(X1) = o_0_0_xboole_0
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(spm,[status(thm)],[c_0_53,c_0_55])).

cnf(c_0_61,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

fof(c_0_62,plain,(
    ! [X53,X54,X55] :
      ( v2_struct_0(X53)
      | ~ v3_orders_2(X53)
      | ~ l1_orders_2(X53)
      | ~ m1_subset_1(X54,u1_struct_0(X53))
      | ~ m1_subset_1(X55,u1_struct_0(X53))
      | r3_orders_2(X53,X54,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[reflexivity_r3_orders_2])])])).

cnf(c_0_63,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_54]),c_0_38])])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ v1_xboole_0(u1_orders_2(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_58]),c_0_37]),c_0_36]),c_0_38])])).

cnf(c_0_65,plain,
    ( u1_orders_2(X1) = o_0_0_xboole_0
    | ~ v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_59,c_0_60]),c_0_46])]),c_0_61])).

fof(c_0_66,plain,(
    ! [X50,X51,X52] :
      ( ( ~ r3_orders_2(X50,X51,X52)
        | r1_orders_2(X50,X51,X52)
        | v2_struct_0(X50)
        | ~ v3_orders_2(X50)
        | ~ l1_orders_2(X50)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X50)) )
      & ( ~ r1_orders_2(X50,X51,X52)
        | r3_orders_2(X50,X51,X52)
        | v2_struct_0(X50)
        | ~ v3_orders_2(X50)
        | ~ l1_orders_2(X50)
        | ~ m1_subset_1(X51,u1_struct_0(X50))
        | ~ m1_subset_1(X52,u1_struct_0(X50)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_67,plain,
    ( v2_struct_0(X1)
    | r3_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_69,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    | ~ l1_struct_0(esk1_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_60]),c_0_46])])).

cnf(c_0_70,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0)
    | ~ v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_46]),c_0_38])])).

cnf(c_0_71,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( r3_orders_2(esk1_0,X1,X1)
    | v2_struct_0(esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_37]),c_0_38]),c_0_68])])).

cnf(c_0_73,negated_conjecture,
    ( ~ v2_struct_0(esk1_0)
    | ~ l1_struct_0(esk1_0) ),
    inference(spm,[status(thm)],[c_0_69,c_0_70])).

fof(c_0_74,plain,(
    ! [X45] : m1_subset_1(esk10_1(X45),X45) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_75,negated_conjecture,
    ( v2_struct_0(esk1_0)
    | r1_orders_2(esk1_0,X1,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_38]),c_0_68])])).

cnf(c_0_76,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_61]),c_0_38])])).

cnf(c_0_77,plain,
    ( m1_subset_1(esk10_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_74])).

fof(c_0_78,plain,(
    ! [X38,X39,X40] :
      ( v1_xboole_0(X38)
      | ~ m1_subset_1(X39,X38)
      | ~ m1_subset_1(X40,X38)
      | m1_subset_1(k7_domain_1(X38,X39,X40),k1_zfmisc_1(X38)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_domain_1])])])).

fof(c_0_79,plain,(
    ! [X47,X48,X49] :
      ( v1_xboole_0(X47)
      | ~ m1_subset_1(X48,X47)
      | ~ m1_subset_1(X49,X47)
      | k7_domain_1(X47,X48,X49) = k2_tarski(X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

cnf(c_0_80,negated_conjecture,
    ( ~ v1_xboole_0(u1_orders_2(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_75]),c_0_38])]),c_0_76])).

cnf(c_0_81,plain,
    ( r3_orders_2(X1,X2,X2)
    | v2_struct_0(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_67,c_0_77])).

fof(c_0_82,plain,(
    ! [X19,X20,X21,X22,X23,X24,X25,X26] :
      ( ( ~ r2_hidden(X22,X21)
        | X22 = X19
        | X22 = X20
        | X21 != k2_tarski(X19,X20) )
      & ( X23 != X19
        | r2_hidden(X23,X21)
        | X21 != k2_tarski(X19,X20) )
      & ( X23 != X20
        | r2_hidden(X23,X21)
        | X21 != k2_tarski(X19,X20) )
      & ( esk5_3(X24,X25,X26) != X24
        | ~ r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k2_tarski(X24,X25) )
      & ( esk5_3(X24,X25,X26) != X25
        | ~ r2_hidden(esk5_3(X24,X25,X26),X26)
        | X26 = k2_tarski(X24,X25) )
      & ( r2_hidden(esk5_3(X24,X25,X26),X26)
        | esk5_3(X24,X25,X26) = X24
        | esk5_3(X24,X25,X26) = X25
        | X26 = k2_tarski(X24,X25) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_83,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_84,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( ~ v1_xboole_0(u1_orders_2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_77])).

cnf(c_0_86,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_71,c_0_81])).

cnf(c_0_87,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_82])).

fof(c_0_88,plain,(
    ! [X12,X13] : k2_tarski(X12,X13) = k2_tarski(X13,X12) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_89,negated_conjecture,
    ( ~ v6_orders_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_90,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_83,c_0_84])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_85,c_0_54]),c_0_38])])).

cnf(c_0_92,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_orders_2(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_86])).

cnf(c_0_93,negated_conjecture,
    ( ~ v6_orders_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r2_hidden(esk3_0,X1)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_94,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_87])])).

cnf(c_0_95,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_96,negated_conjecture,
    ( v6_orders_2(esk4_0,esk1_0)
    | ~ v6_orders_2(X1,esk1_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk1_0)))
    | ~ r2_hidden(esk2_0,X1)
    | ~ r2_hidden(esk3_0,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_97,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r2_hidden(esk2_0,k2_tarski(X1,X2))
    | ~ r2_hidden(esk3_0,k2_tarski(X1,X2))
    | ~ v6_orders_2(k2_tarski(X1,X2),esk1_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_91])).

fof(c_0_98,plain,(
    ! [X60,X61,X62] :
      ( ( ~ v6_orders_2(k7_domain_1(u1_struct_0(X60),X61,X62),X60)
        | ~ m1_subset_1(k7_domain_1(u1_struct_0(X60),X61,X62),k1_zfmisc_1(u1_struct_0(X60)))
        | r3_orders_2(X60,X61,X62)
        | r3_orders_2(X60,X62,X61)
        | ~ m1_subset_1(X62,u1_struct_0(X60))
        | ~ m1_subset_1(X61,u1_struct_0(X60))
        | v2_struct_0(X60)
        | ~ v3_orders_2(X60)
        | ~ l1_orders_2(X60) )
      & ( v6_orders_2(k7_domain_1(u1_struct_0(X60),X61,X62),X60)
        | ~ r3_orders_2(X60,X61,X62)
        | ~ m1_subset_1(X62,u1_struct_0(X60))
        | ~ m1_subset_1(X61,u1_struct_0(X60))
        | v2_struct_0(X60)
        | ~ v3_orders_2(X60)
        | ~ l1_orders_2(X60) )
      & ( m1_subset_1(k7_domain_1(u1_struct_0(X60),X61,X62),k1_zfmisc_1(u1_struct_0(X60)))
        | ~ r3_orders_2(X60,X61,X62)
        | ~ m1_subset_1(X62,u1_struct_0(X60))
        | ~ m1_subset_1(X61,u1_struct_0(X60))
        | v2_struct_0(X60)
        | ~ v3_orders_2(X60)
        | ~ l1_orders_2(X60) )
      & ( v6_orders_2(k7_domain_1(u1_struct_0(X60),X61,X62),X60)
        | ~ r3_orders_2(X60,X62,X61)
        | ~ m1_subset_1(X62,u1_struct_0(X60))
        | ~ m1_subset_1(X61,u1_struct_0(X60))
        | v2_struct_0(X60)
        | ~ v3_orders_2(X60)
        | ~ l1_orders_2(X60) )
      & ( m1_subset_1(k7_domain_1(u1_struct_0(X60),X61,X62),k1_zfmisc_1(u1_struct_0(X60)))
        | ~ r3_orders_2(X60,X62,X61)
        | ~ m1_subset_1(X62,u1_struct_0(X60))
        | ~ m1_subset_1(X61,u1_struct_0(X60))
        | v2_struct_0(X60)
        | ~ v3_orders_2(X60)
        | ~ l1_orders_2(X60) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_orders_2])])])])])).

cnf(c_0_99,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_92,c_0_77])).

cnf(c_0_100,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,k2_tarski(X1,X2))
    | ~ r2_hidden(esk3_0,k2_tarski(X1,X2))
    | ~ v6_orders_2(k2_tarski(X1,X2),esk1_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_93,c_0_90]),c_0_91])).

cnf(c_0_101,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_94,c_0_95])).

fof(c_0_102,plain,(
    ! [X58,X59] :
      ( ~ m1_subset_1(X58,X59)
      | v1_xboole_0(X59)
      | r2_hidden(X58,X59) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_103,negated_conjecture,
    ( v6_orders_2(esk4_0,esk1_0)
    | ~ r2_hidden(esk2_0,k2_tarski(X1,X2))
    | ~ r2_hidden(esk3_0,k2_tarski(X1,X2))
    | ~ v6_orders_2(k2_tarski(X1,X2),esk1_0)
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_90]),c_0_91])).

cnf(c_0_104,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r2_hidden(esk2_0,k2_tarski(X1,esk3_0))
    | ~ v6_orders_2(k2_tarski(X1,esk3_0),esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_97,c_0_94]),c_0_37])])).

cnf(c_0_105,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(X1),X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_98])).

cnf(c_0_106,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_99,c_0_54])).

cnf(c_0_107,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r2_hidden(esk2_0,k2_tarski(esk3_0,X1))
    | ~ v6_orders_2(k2_tarski(esk3_0,X1),esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_37])])).

cnf(c_0_108,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_102])).

cnf(c_0_109,plain,
    ( ~ v1_xboole_0(k2_tarski(X1,X2)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_94])).

fof(c_0_110,plain,(
    ! [X56,X57] :
      ( ~ r2_hidden(X56,X57)
      | m1_subset_1(X56,X57) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_111,negated_conjecture,
    ( v6_orders_2(esk4_0,esk1_0)
    | ~ r2_hidden(esk2_0,k2_tarski(X1,esk3_0))
    | ~ v6_orders_2(k2_tarski(X1,esk3_0),esk1_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_103,c_0_94]),c_0_37])])).

cnf(c_0_112,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ v6_orders_2(k2_tarski(esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_104,c_0_101]),c_0_36])])).

cnf(c_0_113,plain,
    ( v2_struct_0(X1)
    | v6_orders_2(k2_tarski(X2,X3),X1)
    | ~ r3_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_105,c_0_84]),c_0_106])).

cnf(c_0_114,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ v6_orders_2(k2_tarski(esk3_0,X1),esk1_0)
    | ~ m1_subset_1(esk2_0,k2_tarski(esk3_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_107,c_0_108]),c_0_109])).

cnf(c_0_115,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_110])).

cnf(c_0_116,negated_conjecture,
    ( v6_orders_2(esk4_0,esk1_0)
    | ~ v6_orders_2(k2_tarski(esk2_0,esk3_0),esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_111,c_0_101]),c_0_36])])).

fof(c_0_117,plain,(
    ! [X17,X18] :
      ( ( ~ v6_orders_2(X18,X17)
        | r7_relat_2(u1_orders_2(X17),X18)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) )
      & ( ~ r7_relat_2(u1_orders_2(X17),X18)
        | v6_orders_2(X18,X17)
        | ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X17)))
        | ~ l1_orders_2(X17) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

fof(c_0_118,plain,(
    ! [X77,X78,X79] :
      ( ~ m1_subset_1(X79,k1_zfmisc_1(k2_zfmisc_1(X77,X78)))
      | v1_relat_1(X79) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_119,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,esk3_0,esk2_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_112,c_0_113]),c_0_37]),c_0_36]),c_0_38]),c_0_68])]),c_0_76])).

cnf(c_0_120,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_121,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,X1,esk3_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ m1_subset_1(esk2_0,k2_tarski(esk3_0,X1))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_114,c_0_113]),c_0_37]),c_0_38]),c_0_68])]),c_0_76])).

cnf(c_0_122,plain,
    ( m1_subset_1(X1,k2_tarski(X2,X1)) ),
    inference(spm,[status(thm)],[c_0_115,c_0_94])).

cnf(c_0_123,negated_conjecture,
    ( v6_orders_2(esk4_0,esk1_0)
    | ~ r3_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_116,c_0_113]),c_0_37]),c_0_36]),c_0_38]),c_0_68])]),c_0_76])).

fof(c_0_124,plain,(
    ! [X28,X29,X30,X31,X32] :
      ( ( ~ r7_relat_2(X28,X29)
        | ~ r2_hidden(X30,X29)
        | ~ r2_hidden(X31,X29)
        | r2_hidden(k4_tarski(X30,X31),X28)
        | r2_hidden(k4_tarski(X31,X30),X28)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(esk6_2(X28,X32),X32)
        | r7_relat_2(X28,X32)
        | ~ v1_relat_1(X28) )
      & ( r2_hidden(esk7_2(X28,X32),X32)
        | r7_relat_2(X28,X32)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(esk6_2(X28,X32),esk7_2(X28,X32)),X28)
        | r7_relat_2(X28,X32)
        | ~ v1_relat_1(X28) )
      & ( ~ r2_hidden(k4_tarski(esk7_2(X28,X32),esk6_2(X28,X32)),X28)
        | r7_relat_2(X28,X32)
        | ~ v1_relat_1(X28) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_relat_2])])])])])])])).

cnf(c_0_125,plain,
    ( r7_relat_2(u1_orders_2(X2),X1)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_117])).

cnf(c_0_126,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_118])).

cnf(c_0_127,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_119,c_0_120]),c_0_36]),c_0_37]),c_0_38]),c_0_68])]),c_0_76])).

cnf(c_0_128,negated_conjecture,
    ( ~ r3_orders_2(esk1_0,esk2_0,esk3_0)
    | ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_121,c_0_122]),c_0_36])])).

cnf(c_0_129,negated_conjecture,
    ( v6_orders_2(esk4_0,esk1_0)
    | ~ r1_orders_2(esk1_0,esk3_0,esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_123,c_0_120]),c_0_36]),c_0_37]),c_0_38]),c_0_68])]),c_0_76])).

cnf(c_0_130,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | v6_orders_2(esk4_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_131,plain,
    ( r2_hidden(k4_tarski(X3,X4),X1)
    | r2_hidden(k4_tarski(X4,X3),X1)
    | ~ r7_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_124])).

cnf(c_0_132,plain,
    ( r7_relat_2(u1_orders_2(X1),X2)
    | ~ r1_tarski(X2,u1_struct_0(X1))
    | ~ v6_orders_2(X2,X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_125,c_0_43])).

cnf(c_0_133,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_126,c_0_48])).

cnf(c_0_134,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk1_0))
    | r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[c_0_35,c_0_127])).

cnf(c_0_135,negated_conjecture,
    ( ~ r1_orders_2(esk1_0,esk2_0,esk3_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_128,c_0_120]),c_0_37]),c_0_36]),c_0_38]),c_0_68])]),c_0_76])).

cnf(c_0_136,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | v6_orders_2(esk4_0,esk1_0) ),
    inference(spm,[status(thm)],[c_0_129,c_0_130])).

cnf(c_0_137,plain,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | r2_hidden(k4_tarski(X2,X1),u1_orders_2(X3))
    | ~ r1_tarski(X4,u1_struct_0(X3))
    | ~ r2_hidden(X1,X4)
    | ~ r2_hidden(X2,X4)
    | ~ v6_orders_2(X4,X3)
    | ~ l1_orders_2(X3) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_132]),c_0_133])).

cnf(c_0_138,negated_conjecture,
    ( r1_tarski(esk4_0,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[c_0_134,c_0_135])).

cnf(c_0_139,negated_conjecture,
    ( v6_orders_2(esk4_0,esk1_0) ),
    inference(sr,[status(thm)],[c_0_136,c_0_135])).

cnf(c_0_140,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_52,c_0_127])).

cnf(c_0_141,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r1_orders_2(esk1_0,esk3_0,esk2_0)
    | r2_hidden(esk2_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_142,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(esk1_0))
    | r2_hidden(k4_tarski(X2,X1),u1_orders_2(esk1_0))
    | ~ r2_hidden(X2,esk4_0)
    | ~ r2_hidden(X1,esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_137,c_0_138]),c_0_139]),c_0_38])])).

cnf(c_0_143,negated_conjecture,
    ( r2_hidden(esk3_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_140,c_0_135])).

cnf(c_0_144,negated_conjecture,
    ( r1_orders_2(esk1_0,esk2_0,esk3_0)
    | r2_hidden(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_141,c_0_127])).

cnf(c_0_145,negated_conjecture,
    ( r2_hidden(k4_tarski(esk3_0,X1),u1_orders_2(esk1_0))
    | r2_hidden(k4_tarski(X1,esk3_0),u1_orders_2(esk1_0))
    | ~ r2_hidden(X1,esk4_0) ),
    inference(spm,[status(thm)],[c_0_142,c_0_143])).

cnf(c_0_146,negated_conjecture,
    ( r2_hidden(esk2_0,esk4_0) ),
    inference(sr,[status(thm)],[c_0_144,c_0_135])).

cnf(c_0_147,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_148,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk3_0),u1_orders_2(esk1_0))
    | r2_hidden(k4_tarski(esk3_0,esk2_0),u1_orders_2(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_145,c_0_146])).

cnf(c_0_149,negated_conjecture,
    ( r2_hidden(k4_tarski(esk2_0,esk3_0),u1_orders_2(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_148]),c_0_36]),c_0_37]),c_0_38])]),c_0_127])).

cnf(c_0_150,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_147,c_0_149]),c_0_37]),c_0_36]),c_0_38])]),c_0_135]),
    [proof]).
%------------------------------------------------------------------------------
