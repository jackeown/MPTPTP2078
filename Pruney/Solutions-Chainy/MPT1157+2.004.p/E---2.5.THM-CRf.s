%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:09:51 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   77 (2586 expanded)
%              Number of clauses        :   54 ( 894 expanded)
%              Number of leaves         :   11 ( 627 expanded)
%              Depth                    :   13
%              Number of atoms          :  416 (19558 expanded)
%              Number of equality atoms :   48 ( 328 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal clause size      :   58 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t51_orders_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r2_orders_2(X1,X2,X3)
              <=> r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).

fof(t24_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => r1_orders_2(X1,X2,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(t69_enumset1,axiom,(
    ! [X1] : k2_tarski(X1,X1) = k1_tarski(X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(t38_orders_2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).

fof(dt_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(t5_subset,axiom,(
    ! [X1,X2,X3] :
      ~ ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3))
        & v1_xboole_0(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(fraenkel_a_2_0_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X2)
        & v3_orders_2(X2)
        & v4_orders_2(X2)
        & v5_orders_2(X2)
        & l1_orders_2(X2)
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( r2_hidden(X1,a_2_0_orders_2(X2,X3))
      <=> ? [X4] :
            ( m1_subset_1(X4,u1_struct_0(X2))
            & X1 = X4
            & ! [X5] :
                ( m1_subset_1(X5,u1_struct_0(X2))
               => ( r2_hidden(X5,X3)
                 => r2_orders_2(X2,X5,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(d12_orders_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(c_0_11,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ( r2_orders_2(X1,X2,X3)
                <=> r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t51_orders_2])).

fof(c_0_12,plain,(
    ! [X35,X36] :
      ( v2_struct_0(X35)
      | ~ v3_orders_2(X35)
      | ~ l1_orders_2(X35)
      | ~ m1_subset_1(X36,u1_struct_0(X35))
      | r1_orders_2(X35,X36,X36) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).

fof(c_0_13,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v3_orders_2(esk5_0)
    & v4_orders_2(esk5_0)
    & v5_orders_2(esk5_0)
    & l1_orders_2(esk5_0)
    & m1_subset_1(esk6_0,u1_struct_0(esk5_0))
    & m1_subset_1(esk7_0,u1_struct_0(esk5_0))
    & ( ~ r2_orders_2(esk5_0,esk6_0,esk7_0)
      | ~ r2_hidden(esk7_0,k1_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) )
    & ( r2_orders_2(esk5_0,esk6_0,esk7_0)
      | r2_hidden(esk7_0,k1_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).

fof(c_0_14,plain,(
    ! [X33,X34] :
      ( v1_xboole_0(X33)
      | ~ m1_subset_1(X34,X33)
      | k6_domain_1(X33,X34) = k1_tarski(X34) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

fof(c_0_15,plain,(
    ! [X15] : k2_tarski(X15,X15) = k1_tarski(X15) ),
    inference(variable_rename,[status(thm)],[t69_enumset1])).

fof(c_0_16,plain,(
    ! [X37,X38,X39,X40] :
      ( ( ~ v6_orders_2(X40,X37)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X37)))
        | ~ r2_hidden(X38,X40)
        | ~ r2_hidden(X39,X40)
        | r1_orders_2(X37,X38,X39)
        | r1_orders_2(X37,X39,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( v6_orders_2(esk4_3(X37,X38,X39),X37)
        | ~ r1_orders_2(X37,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( m1_subset_1(esk4_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X37)))
        | ~ r1_orders_2(X37,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( r2_hidden(X38,esk4_3(X37,X38,X39))
        | ~ r1_orders_2(X37,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( r2_hidden(X39,esk4_3(X37,X38,X39))
        | ~ r1_orders_2(X37,X38,X39)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( v6_orders_2(esk4_3(X37,X38,X39),X37)
        | ~ r1_orders_2(X37,X39,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( m1_subset_1(esk4_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X37)))
        | ~ r1_orders_2(X37,X39,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( r2_hidden(X38,esk4_3(X37,X38,X39))
        | ~ r1_orders_2(X37,X39,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ l1_orders_2(X37) )
      & ( r2_hidden(X39,esk4_3(X37,X38,X39))
        | ~ r1_orders_2(X37,X39,X38)
        | ~ m1_subset_1(X39,u1_struct_0(X37))
        | ~ m1_subset_1(X38,u1_struct_0(X37))
        | ~ v3_orders_2(X37)
        | ~ l1_orders_2(X37) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_orders_2])])])])])])).

cnf(c_0_17,plain,
    ( v2_struct_0(X1)
    | r1_orders_2(X1,X2,X2)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk7_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_19,negated_conjecture,
    ( l1_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_20,negated_conjecture,
    ( v3_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

fof(c_0_22,plain,(
    ! [X24,X25] :
      ( v1_xboole_0(X24)
      | ~ m1_subset_1(X25,X24)
      | m1_subset_1(k6_domain_1(X24,X25),k1_zfmisc_1(X24)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_14])).

cnf(c_0_24,plain,
    ( k2_tarski(X1,X1) = k1_tarski(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_15])).

fof(c_0_25,plain,(
    ! [X19,X20,X21] :
      ( ~ r2_hidden(X19,X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(X21))
      | ~ v1_xboole_0(X21) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).

cnf(c_0_26,plain,
    ( r2_hidden(X1,esk4_3(X2,X3,X1))
    | ~ r1_orders_2(X2,X3,X1)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_27,negated_conjecture,
    ( r1_orders_2(esk5_0,esk7_0,esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19]),c_0_20])]),c_0_21])).

fof(c_0_28,plain,(
    ! [X26,X27,X28,X30,X31] :
      ( ( m1_subset_1(esk2_3(X26,X27,X28),u1_struct_0(X27))
        | ~ r2_hidden(X26,a_2_0_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( X26 = esk2_3(X26,X27,X28)
        | ~ r2_hidden(X26,a_2_0_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( ~ m1_subset_1(X30,u1_struct_0(X27))
        | ~ r2_hidden(X30,X28)
        | r2_orders_2(X27,X30,esk2_3(X26,X27,X28))
        | ~ r2_hidden(X26,a_2_0_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( m1_subset_1(esk3_4(X26,X27,X28,X31),u1_struct_0(X27))
        | ~ m1_subset_1(X31,u1_struct_0(X27))
        | X26 != X31
        | r2_hidden(X26,a_2_0_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( r2_hidden(esk3_4(X26,X27,X28,X31),X28)
        | ~ m1_subset_1(X31,u1_struct_0(X27))
        | X26 != X31
        | r2_hidden(X26,a_2_0_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) )
      & ( ~ r2_orders_2(X27,esk3_4(X26,X27,X28,X31),X31)
        | ~ m1_subset_1(X31,u1_struct_0(X27))
        | X26 != X31
        | r2_hidden(X26,a_2_0_orders_2(X27,X28))
        | v2_struct_0(X27)
        | ~ v3_orders_2(X27)
        | ~ v4_orders_2(X27)
        | ~ v5_orders_2(X27)
        | ~ l1_orders_2(X27)
        | ~ m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).

cnf(c_0_29,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk5_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_31,plain,
    ( k6_domain_1(X1,X2) = k2_tarski(X2,X2)
    | v1_xboole_0(X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(rw,[status(thm)],[c_0_23,c_0_24])).

cnf(c_0_32,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3))
    | ~ v1_xboole_0(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_33,negated_conjecture,
    ( r2_hidden(esk7_0,esk4_3(esk5_0,esk7_0,esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_27]),c_0_19]),c_0_20]),c_0_18])])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r1_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_35,plain,
    ( r2_hidden(esk3_4(X1,X2,X3,X4),X3)
    | r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | X1 != X4
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_36,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_37,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk6_0) = k2_tarski(esk6_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_31,c_0_30])).

cnf(c_0_38,negated_conjecture,
    ( ~ v1_xboole_0(X1)
    | ~ m1_subset_1(esk4_3(esk5_0,esk7_0,esk7_0),k1_zfmisc_1(X1)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_39,negated_conjecture,
    ( m1_subset_1(esk4_3(esk5_0,esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_27]),c_0_19]),c_0_20]),c_0_18])])).

fof(c_0_40,plain,(
    ! [X22,X23] :
      ( v2_struct_0(X22)
      | ~ v3_orders_2(X22)
      | ~ v4_orders_2(X22)
      | ~ v5_orders_2(X22)
      | ~ l1_orders_2(X22)
      | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))
      | k1_orders_2(X22,X23) = a_2_0_orders_2(X22,X23) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).

fof(c_0_41,plain,(
    ! [X6,X7,X8,X9,X10,X11,X12,X13] :
      ( ( ~ r2_hidden(X9,X8)
        | X9 = X6
        | X9 = X7
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X6
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( X10 != X7
        | r2_hidden(X10,X8)
        | X8 != k2_tarski(X6,X7) )
      & ( esk1_3(X11,X12,X13) != X11
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( esk1_3(X11,X12,X13) != X12
        | ~ r2_hidden(esk1_3(X11,X12,X13),X13)
        | X13 = k2_tarski(X11,X12) )
      & ( r2_hidden(esk1_3(X11,X12,X13),X13)
        | esk1_3(X11,X12,X13) = X11
        | esk1_3(X11,X12,X13) = X12
        | X13 = k2_tarski(X11,X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_42,plain,
    ( v2_struct_0(X1)
    | r2_hidden(esk3_4(X2,X1,X3,X2),X3)
    | r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_35])).

cnf(c_0_43,negated_conjecture,
    ( v5_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_44,negated_conjecture,
    ( v4_orders_2(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_45,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk5_0))
    | m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(spm,[status(thm)],[c_0_36,c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(spm,[status(thm)],[c_0_38,c_0_39])).

cnf(c_0_47,plain,
    ( v2_struct_0(X1)
    | k1_orders_2(X1,X2) = a_2_0_orders_2(X1,X2)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_40])).

cnf(c_0_48,plain,
    ( X1 = X3
    | X1 = X4
    | ~ r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_49,negated_conjecture,
    ( r2_hidden(esk3_4(esk7_0,esk5_0,X1,esk7_0),X1)
    | r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,X1))
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_18]),c_0_19]),c_0_43]),c_0_44]),c_0_20])]),c_0_21])).

cnf(c_0_50,negated_conjecture,
    ( m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(sr,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_51,negated_conjecture,
    ( r2_orders_2(esk5_0,esk6_0,esk7_0)
    | r2_hidden(esk7_0,k1_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_52,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk5_0),esk6_0) = k2_tarski(esk6_0,esk6_0) ),
    inference(sr,[status(thm)],[c_0_37,c_0_46])).

cnf(c_0_53,negated_conjecture,
    ( k1_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)) = a_2_0_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))
    | v1_xboole_0(u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_36]),c_0_19]),c_0_43]),c_0_44]),c_0_20])]),c_0_21])).

fof(c_0_54,plain,(
    ! [X16,X17,X18] :
      ( ~ r2_hidden(X16,X17)
      | ~ m1_subset_1(X17,k1_zfmisc_1(X18))
      | m1_subset_1(X16,X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

cnf(c_0_55,plain,
    ( r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | v2_struct_0(X1)
    | ~ r2_orders_2(X1,esk3_4(X2,X1,X3,X4),X4)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | X2 != X4
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_56,plain,
    ( X1 = X2
    | X1 = X3
    | ~ r2_hidden(X1,k2_tarski(X3,X2)) ),
    inference(er,[status(thm)],[c_0_48])).

cnf(c_0_57,negated_conjecture,
    ( r2_hidden(esk3_4(esk7_0,esk5_0,k2_tarski(esk6_0,esk6_0),esk7_0),k2_tarski(esk6_0,esk6_0))
    | r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_49,c_0_50])).

cnf(c_0_58,negated_conjecture,
    ( r2_orders_2(esk5_0,esk6_0,esk7_0)
    | r2_hidden(esk7_0,k1_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_59,negated_conjecture,
    ( k1_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0)) = a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_53,c_0_46]),c_0_52]),c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( ~ r2_orders_2(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(esk7_0,k1_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_61,plain,
    ( r2_orders_2(X2,X1,esk2_3(X4,X2,X3))
    | v2_struct_0(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ r2_hidden(X1,X3)
    | ~ r2_hidden(X4,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_63,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_41])).

cnf(c_0_64,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X2,a_2_0_orders_2(X1,X3))
    | ~ r2_orders_2(X1,esk3_4(X2,X1,X3,X2),X2)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(er,[status(thm)],[c_0_55])).

cnf(c_0_65,negated_conjecture,
    ( esk3_4(esk7_0,esk5_0,k2_tarski(esk6_0,esk6_0),esk7_0) = esk6_0
    | r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(spm,[status(thm)],[c_0_56,c_0_57])).

cnf(c_0_66,negated_conjecture,
    ( r2_orders_2(esk5_0,esk6_0,esk7_0)
    | r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_orders_2(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(esk7_0,k1_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_60,c_0_52])).

cnf(c_0_68,plain,
    ( r2_orders_2(X1,X2,esk2_3(X3,X1,X4))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,X4))
    | ~ r2_hidden(X2,X4) ),
    inference(csr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_69,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_63])])).

cnf(c_0_70,plain,
    ( X1 = esk2_3(X1,X2,X3)
    | v2_struct_0(X2)
    | ~ r2_hidden(X1,a_2_0_orders_2(X2,X3))
    | ~ v3_orders_2(X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_71,negated_conjecture,
    ( r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_65]),c_0_19]),c_0_43]),c_0_44]),c_0_20]),c_0_50]),c_0_18])]),c_0_21]),c_0_66])).

cnf(c_0_72,negated_conjecture,
    ( ~ r2_orders_2(esk5_0,esk6_0,esk7_0)
    | ~ r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0))) ),
    inference(rw,[status(thm)],[c_0_67,c_0_59])).

cnf(c_0_73,plain,
    ( r2_orders_2(X1,X2,esk2_3(X3,X1,k2_tarski(X4,X2)))
    | v2_struct_0(X1)
    | ~ l1_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1)
    | ~ m1_subset_1(k2_tarski(X4,X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,a_2_0_orders_2(X1,k2_tarski(X4,X2))) ),
    inference(spm,[status(thm)],[c_0_68,c_0_69])).

cnf(c_0_74,negated_conjecture,
    ( esk2_3(esk7_0,esk5_0,k2_tarski(esk6_0,esk6_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70,c_0_71]),c_0_19]),c_0_43]),c_0_44]),c_0_20]),c_0_50])]),c_0_21])).

cnf(c_0_75,negated_conjecture,
    ( ~ r2_orders_2(esk5_0,esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72,c_0_71])])).

cnf(c_0_76,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73,c_0_71]),c_0_74]),c_0_19]),c_0_43]),c_0_44]),c_0_20]),c_0_50])]),c_0_75]),c_0_21]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  # Version: 2.5pre002
% 0.13/0.35  # No SInE strategy applied
% 0.13/0.35  # Trying AutoSched0 for 299 seconds
% 0.19/0.41  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.19/0.41  # and selection function SelectCQIPrecWNTNp.
% 0.19/0.41  #
% 0.19/0.41  # Preprocessing time       : 0.029 s
% 0.19/0.41  # Presaturation interreduction done
% 0.19/0.41  
% 0.19/0.41  # Proof found!
% 0.19/0.41  # SZS status Theorem
% 0.19/0.41  # SZS output start CNFRefutation
% 0.19/0.41  fof(t51_orders_2, conjecture, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_orders_2)).
% 0.19/0.41  fof(t24_orders_2, axiom, ![X1]:(((~(v2_struct_0(X1))&v3_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>r1_orders_2(X1,X2,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_orders_2)).
% 0.19/0.41  fof(redefinition_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>k6_domain_1(X1,X2)=k1_tarski(X2)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 0.19/0.41  fof(t69_enumset1, axiom, ![X1]:k2_tarski(X1,X1)=k1_tarski(X1), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 0.19/0.41  fof(t38_orders_2, axiom, ![X1]:((v3_orders_2(X1)&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(~(((?[X4]:(((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))&r2_hidden(X2,X4))&r2_hidden(X3,X4))&~(r1_orders_2(X1,X2,X3)))&~(r1_orders_2(X1,X3,X2))))&~(((r1_orders_2(X1,X2,X3)|r1_orders_2(X1,X3,X2))&![X4]:((v6_orders_2(X4,X1)&m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))))=>~((r2_hidden(X2,X4)&r2_hidden(X3,X4)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_orders_2)).
% 0.19/0.41  fof(dt_k6_domain_1, axiom, ![X1, X2]:((~(v1_xboole_0(X1))&m1_subset_1(X2,X1))=>m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 0.19/0.41  fof(t5_subset, axiom, ![X1, X2, X3]:~(((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))&v1_xboole_0(X3))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 0.19/0.41  fof(fraenkel_a_2_0_orders_2, axiom, ![X1, X2, X3]:((((((~(v2_struct_0(X2))&v3_orders_2(X2))&v4_orders_2(X2))&v5_orders_2(X2))&l1_orders_2(X2))&m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))))=>(r2_hidden(X1,a_2_0_orders_2(X2,X3))<=>?[X4]:((m1_subset_1(X4,u1_struct_0(X2))&X1=X4)&![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>(r2_hidden(X5,X3)=>r2_orders_2(X2,X5,X4)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fraenkel_a_2_0_orders_2)).
% 0.19/0.41  fof(d12_orders_2, axiom, ![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d12_orders_2)).
% 0.19/0.41  fof(d2_tarski, axiom, ![X1, X2, X3]:(X3=k2_tarski(X1,X2)<=>![X4]:(r2_hidden(X4,X3)<=>(X4=X1|X4=X2))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 0.19/0.41  fof(t4_subset, axiom, ![X1, X2, X3]:((r2_hidden(X1,X2)&m1_subset_1(X2,k1_zfmisc_1(X3)))=>m1_subset_1(X1,X3)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 0.19/0.41  fof(c_0_11, negated_conjecture, ~(![X1]:(((((~(v2_struct_0(X1))&v3_orders_2(X1))&v4_orders_2(X1))&v5_orders_2(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r2_orders_2(X1,X2,X3)<=>r2_hidden(X3,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))))))), inference(assume_negation,[status(cth)],[t51_orders_2])).
% 0.19/0.41  fof(c_0_12, plain, ![X35, X36]:(v2_struct_0(X35)|~v3_orders_2(X35)|~l1_orders_2(X35)|(~m1_subset_1(X36,u1_struct_0(X35))|r1_orders_2(X35,X36,X36))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t24_orders_2])])])])).
% 0.19/0.41  fof(c_0_13, negated_conjecture, (((((~v2_struct_0(esk5_0)&v3_orders_2(esk5_0))&v4_orders_2(esk5_0))&v5_orders_2(esk5_0))&l1_orders_2(esk5_0))&(m1_subset_1(esk6_0,u1_struct_0(esk5_0))&(m1_subset_1(esk7_0,u1_struct_0(esk5_0))&((~r2_orders_2(esk5_0,esk6_0,esk7_0)|~r2_hidden(esk7_0,k1_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))))&(r2_orders_2(esk5_0,esk6_0,esk7_0)|r2_hidden(esk7_0,k1_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_11])])])])).
% 0.19/0.41  fof(c_0_14, plain, ![X33, X34]:(v1_xboole_0(X33)|~m1_subset_1(X34,X33)|k6_domain_1(X33,X34)=k1_tarski(X34)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).
% 0.19/0.41  fof(c_0_15, plain, ![X15]:k2_tarski(X15,X15)=k1_tarski(X15), inference(variable_rename,[status(thm)],[t69_enumset1])).
% 0.19/0.41  fof(c_0_16, plain, ![X37, X38, X39, X40]:((~v6_orders_2(X40,X37)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X37)))|~r2_hidden(X38,X40)|~r2_hidden(X39,X40)|r1_orders_2(X37,X38,X39)|r1_orders_2(X37,X39,X38)|~m1_subset_1(X39,u1_struct_0(X37))|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~l1_orders_2(X37)))&((((v6_orders_2(esk4_3(X37,X38,X39),X37)|~r1_orders_2(X37,X38,X39)|~m1_subset_1(X39,u1_struct_0(X37))|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~l1_orders_2(X37)))&(m1_subset_1(esk4_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X37)))|~r1_orders_2(X37,X38,X39)|~m1_subset_1(X39,u1_struct_0(X37))|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~l1_orders_2(X37))))&((r2_hidden(X38,esk4_3(X37,X38,X39))|~r1_orders_2(X37,X38,X39)|~m1_subset_1(X39,u1_struct_0(X37))|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~l1_orders_2(X37)))&(r2_hidden(X39,esk4_3(X37,X38,X39))|~r1_orders_2(X37,X38,X39)|~m1_subset_1(X39,u1_struct_0(X37))|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~l1_orders_2(X37)))))&(((v6_orders_2(esk4_3(X37,X38,X39),X37)|~r1_orders_2(X37,X39,X38)|~m1_subset_1(X39,u1_struct_0(X37))|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~l1_orders_2(X37)))&(m1_subset_1(esk4_3(X37,X38,X39),k1_zfmisc_1(u1_struct_0(X37)))|~r1_orders_2(X37,X39,X38)|~m1_subset_1(X39,u1_struct_0(X37))|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~l1_orders_2(X37))))&((r2_hidden(X38,esk4_3(X37,X38,X39))|~r1_orders_2(X37,X39,X38)|~m1_subset_1(X39,u1_struct_0(X37))|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~l1_orders_2(X37)))&(r2_hidden(X39,esk4_3(X37,X38,X39))|~r1_orders_2(X37,X39,X38)|~m1_subset_1(X39,u1_struct_0(X37))|~m1_subset_1(X38,u1_struct_0(X37))|(~v3_orders_2(X37)|~l1_orders_2(X37))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t38_orders_2])])])])])])).
% 0.19/0.41  cnf(c_0_17, plain, (v2_struct_0(X1)|r1_orders_2(X1,X2,X2)|~v3_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_12])).
% 0.19/0.41  cnf(c_0_18, negated_conjecture, (m1_subset_1(esk7_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_19, negated_conjecture, (l1_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_20, negated_conjecture, (v3_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_21, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  fof(c_0_22, plain, ![X24, X25]:(v1_xboole_0(X24)|~m1_subset_1(X25,X24)|m1_subset_1(k6_domain_1(X24,X25),k1_zfmisc_1(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_domain_1])])])).
% 0.19/0.41  cnf(c_0_23, plain, (v1_xboole_0(X1)|k6_domain_1(X1,X2)=k1_tarski(X2)|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_14])).
% 0.19/0.41  cnf(c_0_24, plain, (k2_tarski(X1,X1)=k1_tarski(X1)), inference(split_conjunct,[status(thm)],[c_0_15])).
% 0.19/0.41  fof(c_0_25, plain, ![X19, X20, X21]:(~r2_hidden(X19,X20)|~m1_subset_1(X20,k1_zfmisc_1(X21))|~v1_xboole_0(X21)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t5_subset])])).
% 0.19/0.41  cnf(c_0_26, plain, (r2_hidden(X1,esk4_3(X2,X3,X1))|~r1_orders_2(X2,X3,X1)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))|~v3_orders_2(X2)|~l1_orders_2(X2)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_27, negated_conjecture, (r1_orders_2(esk5_0,esk7_0,esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17, c_0_18]), c_0_19]), c_0_20])]), c_0_21])).
% 0.19/0.41  fof(c_0_28, plain, ![X26, X27, X28, X30, X31]:((((m1_subset_1(esk2_3(X26,X27,X28),u1_struct_0(X27))|~r2_hidden(X26,a_2_0_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))&(X26=esk2_3(X26,X27,X28)|~r2_hidden(X26,a_2_0_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))))))&(~m1_subset_1(X30,u1_struct_0(X27))|(~r2_hidden(X30,X28)|r2_orders_2(X27,X30,esk2_3(X26,X27,X28)))|~r2_hidden(X26,a_2_0_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27))))))&((m1_subset_1(esk3_4(X26,X27,X28,X31),u1_struct_0(X27))|(~m1_subset_1(X31,u1_struct_0(X27))|X26!=X31)|r2_hidden(X26,a_2_0_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))&((r2_hidden(esk3_4(X26,X27,X28,X31),X28)|(~m1_subset_1(X31,u1_struct_0(X27))|X26!=X31)|r2_hidden(X26,a_2_0_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))&(~r2_orders_2(X27,esk3_4(X26,X27,X28,X31),X31)|(~m1_subset_1(X31,u1_struct_0(X27))|X26!=X31)|r2_hidden(X26,a_2_0_orders_2(X27,X28))|(v2_struct_0(X27)|~v3_orders_2(X27)|~v4_orders_2(X27)|~v5_orders_2(X27)|~l1_orders_2(X27)|~m1_subset_1(X28,k1_zfmisc_1(u1_struct_0(X27)))))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fraenkel_a_2_0_orders_2])])])])])])).
% 0.19/0.41  cnf(c_0_29, plain, (v1_xboole_0(X1)|m1_subset_1(k6_domain_1(X1,X2),k1_zfmisc_1(X1))|~m1_subset_1(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_22])).
% 0.19/0.41  cnf(c_0_30, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk5_0))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_31, plain, (k6_domain_1(X1,X2)=k2_tarski(X2,X2)|v1_xboole_0(X1)|~m1_subset_1(X2,X1)), inference(rw,[status(thm)],[c_0_23, c_0_24])).
% 0.19/0.41  cnf(c_0_32, plain, (~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))|~v1_xboole_0(X3)), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.41  cnf(c_0_33, negated_conjecture, (r2_hidden(esk7_0,esk4_3(esk5_0,esk7_0,esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_27]), c_0_19]), c_0_20]), c_0_18])])).
% 0.19/0.41  cnf(c_0_34, plain, (m1_subset_1(esk4_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))|~r1_orders_2(X1,X3,X2)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.19/0.41  cnf(c_0_35, plain, (r2_hidden(esk3_4(X1,X2,X3,X4),X3)|r2_hidden(X1,a_2_0_orders_2(X2,X3))|v2_struct_0(X2)|~m1_subset_1(X4,u1_struct_0(X2))|X1!=X4|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_36, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|m1_subset_1(k6_domain_1(u1_struct_0(esk5_0),esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.19/0.41  cnf(c_0_37, negated_conjecture, (k6_domain_1(u1_struct_0(esk5_0),esk6_0)=k2_tarski(esk6_0,esk6_0)|v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_31, c_0_30])).
% 0.19/0.41  cnf(c_0_38, negated_conjecture, (~v1_xboole_0(X1)|~m1_subset_1(esk4_3(esk5_0,esk7_0,esk7_0),k1_zfmisc_1(X1))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.19/0.41  cnf(c_0_39, negated_conjecture, (m1_subset_1(esk4_3(esk5_0,esk7_0,esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_27]), c_0_19]), c_0_20]), c_0_18])])).
% 0.19/0.41  fof(c_0_40, plain, ![X22, X23]:(v2_struct_0(X22)|~v3_orders_2(X22)|~v4_orders_2(X22)|~v5_orders_2(X22)|~l1_orders_2(X22)|(~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))|k1_orders_2(X22,X23)=a_2_0_orders_2(X22,X23))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d12_orders_2])])])])).
% 0.19/0.41  fof(c_0_41, plain, ![X6, X7, X8, X9, X10, X11, X12, X13]:(((~r2_hidden(X9,X8)|(X9=X6|X9=X7)|X8!=k2_tarski(X6,X7))&((X10!=X6|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))&(X10!=X7|r2_hidden(X10,X8)|X8!=k2_tarski(X6,X7))))&(((esk1_3(X11,X12,X13)!=X11|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12))&(esk1_3(X11,X12,X13)!=X12|~r2_hidden(esk1_3(X11,X12,X13),X13)|X13=k2_tarski(X11,X12)))&(r2_hidden(esk1_3(X11,X12,X13),X13)|(esk1_3(X11,X12,X13)=X11|esk1_3(X11,X12,X13)=X12)|X13=k2_tarski(X11,X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).
% 0.19/0.41  cnf(c_0_42, plain, (v2_struct_0(X1)|r2_hidden(esk3_4(X2,X1,X3,X2),X3)|r2_hidden(X2,a_2_0_orders_2(X1,X3))|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_35])).
% 0.19/0.41  cnf(c_0_43, negated_conjecture, (v5_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_44, negated_conjecture, (v4_orders_2(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_45, negated_conjecture, (v1_xboole_0(u1_struct_0(esk5_0))|m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(spm,[status(thm)],[c_0_36, c_0_37])).
% 0.19/0.41  cnf(c_0_46, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk5_0))), inference(spm,[status(thm)],[c_0_38, c_0_39])).
% 0.19/0.41  cnf(c_0_47, plain, (v2_struct_0(X1)|k1_orders_2(X1,X2)=a_2_0_orders_2(X1,X2)|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_40])).
% 0.19/0.41  cnf(c_0_48, plain, (X1=X3|X1=X4|~r2_hidden(X1,X2)|X2!=k2_tarski(X3,X4)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.41  cnf(c_0_49, negated_conjecture, (r2_hidden(esk3_4(esk7_0,esk5_0,X1,esk7_0),X1)|r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,X1))|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42, c_0_18]), c_0_19]), c_0_43]), c_0_44]), c_0_20])]), c_0_21])).
% 0.19/0.41  cnf(c_0_50, negated_conjecture, (m1_subset_1(k2_tarski(esk6_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(sr,[status(thm)],[c_0_45, c_0_46])).
% 0.19/0.41  cnf(c_0_51, negated_conjecture, (r2_orders_2(esk5_0,esk6_0,esk7_0)|r2_hidden(esk7_0,k1_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_52, negated_conjecture, (k6_domain_1(u1_struct_0(esk5_0),esk6_0)=k2_tarski(esk6_0,esk6_0)), inference(sr,[status(thm)],[c_0_37, c_0_46])).
% 0.19/0.41  cnf(c_0_53, negated_conjecture, (k1_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))=a_2_0_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0))|v1_xboole_0(u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_36]), c_0_19]), c_0_43]), c_0_44]), c_0_20])]), c_0_21])).
% 0.19/0.41  fof(c_0_54, plain, ![X16, X17, X18]:(~r2_hidden(X16,X17)|~m1_subset_1(X17,k1_zfmisc_1(X18))|m1_subset_1(X16,X18)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).
% 0.19/0.41  cnf(c_0_55, plain, (r2_hidden(X2,a_2_0_orders_2(X1,X3))|v2_struct_0(X1)|~r2_orders_2(X1,esk3_4(X2,X1,X3,X4),X4)|~m1_subset_1(X4,u1_struct_0(X1))|X2!=X4|~v3_orders_2(X1)|~v4_orders_2(X1)|~v5_orders_2(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_56, plain, (X1=X2|X1=X3|~r2_hidden(X1,k2_tarski(X3,X2))), inference(er,[status(thm)],[c_0_48])).
% 0.19/0.41  cnf(c_0_57, negated_conjecture, (r2_hidden(esk3_4(esk7_0,esk5_0,k2_tarski(esk6_0,esk6_0),esk7_0),k2_tarski(esk6_0,esk6_0))|r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_49, c_0_50])).
% 0.19/0.41  cnf(c_0_58, negated_conjecture, (r2_orders_2(esk5_0,esk6_0,esk7_0)|r2_hidden(esk7_0,k1_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0)))), inference(rw,[status(thm)],[c_0_51, c_0_52])).
% 0.19/0.41  cnf(c_0_59, negated_conjecture, (k1_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0))=a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0))), inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(sr,[status(thm)],[c_0_53, c_0_46]), c_0_52]), c_0_52])).
% 0.19/0.41  cnf(c_0_60, negated_conjecture, (~r2_orders_2(esk5_0,esk6_0,esk7_0)|~r2_hidden(esk7_0,k1_orders_2(esk5_0,k6_domain_1(u1_struct_0(esk5_0),esk6_0)))), inference(split_conjunct,[status(thm)],[c_0_13])).
% 0.19/0.41  cnf(c_0_61, plain, (r2_orders_2(X2,X1,esk2_3(X4,X2,X3))|v2_struct_0(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~r2_hidden(X1,X3)|~r2_hidden(X4,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_62, plain, (m1_subset_1(X1,X3)|~r2_hidden(X1,X2)|~m1_subset_1(X2,k1_zfmisc_1(X3))), inference(split_conjunct,[status(thm)],[c_0_54])).
% 0.19/0.41  cnf(c_0_63, plain, (r2_hidden(X1,X3)|X1!=X2|X3!=k2_tarski(X4,X2)), inference(split_conjunct,[status(thm)],[c_0_41])).
% 0.19/0.41  cnf(c_0_64, plain, (v2_struct_0(X1)|r2_hidden(X2,a_2_0_orders_2(X1,X3))|~r2_orders_2(X1,esk3_4(X2,X1,X3,X2),X2)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X2,u1_struct_0(X1))), inference(er,[status(thm)],[c_0_55])).
% 0.19/0.41  cnf(c_0_65, negated_conjecture, (esk3_4(esk7_0,esk5_0,k2_tarski(esk6_0,esk6_0),esk7_0)=esk6_0|r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0)))), inference(spm,[status(thm)],[c_0_56, c_0_57])).
% 0.19/0.41  cnf(c_0_66, negated_conjecture, (r2_orders_2(esk5_0,esk6_0,esk7_0)|r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0)))), inference(rw,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.41  cnf(c_0_67, negated_conjecture, (~r2_orders_2(esk5_0,esk6_0,esk7_0)|~r2_hidden(esk7_0,k1_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0)))), inference(rw,[status(thm)],[c_0_60, c_0_52])).
% 0.19/0.41  cnf(c_0_68, plain, (r2_orders_2(X1,X2,esk2_3(X3,X1,X4))|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,a_2_0_orders_2(X1,X4))|~r2_hidden(X2,X4)), inference(csr,[status(thm)],[c_0_61, c_0_62])).
% 0.19/0.41  cnf(c_0_69, plain, (r2_hidden(X1,k2_tarski(X2,X1))), inference(er,[status(thm)],[inference(er,[status(thm)],[c_0_63])])).
% 0.19/0.41  cnf(c_0_70, plain, (X1=esk2_3(X1,X2,X3)|v2_struct_0(X2)|~r2_hidden(X1,a_2_0_orders_2(X2,X3))|~v3_orders_2(X2)|~v4_orders_2(X2)|~v5_orders_2(X2)|~l1_orders_2(X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.19/0.41  cnf(c_0_71, negated_conjecture, (r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0)))), inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_65]), c_0_19]), c_0_43]), c_0_44]), c_0_20]), c_0_50]), c_0_18])]), c_0_21]), c_0_66])).
% 0.19/0.41  cnf(c_0_72, negated_conjecture, (~r2_orders_2(esk5_0,esk6_0,esk7_0)|~r2_hidden(esk7_0,a_2_0_orders_2(esk5_0,k2_tarski(esk6_0,esk6_0)))), inference(rw,[status(thm)],[c_0_67, c_0_59])).
% 0.19/0.41  cnf(c_0_73, plain, (r2_orders_2(X1,X2,esk2_3(X3,X1,k2_tarski(X4,X2)))|v2_struct_0(X1)|~l1_orders_2(X1)|~v5_orders_2(X1)|~v4_orders_2(X1)|~v3_orders_2(X1)|~m1_subset_1(k2_tarski(X4,X2),k1_zfmisc_1(u1_struct_0(X1)))|~r2_hidden(X3,a_2_0_orders_2(X1,k2_tarski(X4,X2)))), inference(spm,[status(thm)],[c_0_68, c_0_69])).
% 0.19/0.41  cnf(c_0_74, negated_conjecture, (esk2_3(esk7_0,esk5_0,k2_tarski(esk6_0,esk6_0))=esk7_0), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_70, c_0_71]), c_0_19]), c_0_43]), c_0_44]), c_0_20]), c_0_50])]), c_0_21])).
% 0.19/0.41  cnf(c_0_75, negated_conjecture, (~r2_orders_2(esk5_0,esk6_0,esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_72, c_0_71])])).
% 0.19/0.41  cnf(c_0_76, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_73, c_0_71]), c_0_74]), c_0_19]), c_0_43]), c_0_44]), c_0_20]), c_0_50])]), c_0_75]), c_0_21]), ['proof']).
% 0.19/0.41  # SZS output end CNFRefutation
% 0.19/0.41  # Proof object total steps             : 77
% 0.19/0.41  # Proof object clause steps            : 54
% 0.19/0.41  # Proof object formula steps           : 23
% 0.19/0.41  # Proof object conjectures             : 35
% 0.19/0.41  # Proof object clause conjectures      : 32
% 0.19/0.41  # Proof object formula conjectures     : 3
% 0.19/0.41  # Proof object initial clauses used    : 24
% 0.19/0.41  # Proof object initial formulas used   : 11
% 0.19/0.41  # Proof object generating inferences   : 16
% 0.19/0.41  # Proof object simplifying inferences  : 67
% 0.19/0.41  # Training examples: 0 positive, 0 negative
% 0.19/0.41  # Parsed axioms                        : 11
% 0.19/0.41  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.41  # Initial clauses                      : 37
% 0.19/0.41  # Removed in clause preprocessing      : 1
% 0.19/0.41  # Initial clauses in saturation        : 36
% 0.19/0.41  # Processed clauses                    : 325
% 0.19/0.41  # ...of these trivial                  : 7
% 0.19/0.41  # ...subsumed                          : 61
% 0.19/0.41  # ...remaining for further processing  : 257
% 0.19/0.41  # Other redundant clauses eliminated   : 26
% 0.19/0.41  # Clauses deleted for lack of memory   : 0
% 0.19/0.41  # Backward-subsumed                    : 0
% 0.19/0.41  # Backward-rewritten                   : 22
% 0.19/0.41  # Generated clauses                    : 752
% 0.19/0.41  # ...of the previous two non-trivial   : 641
% 0.19/0.41  # Contextual simplify-reflections      : 14
% 0.19/0.41  # Paramodulations                      : 705
% 0.19/0.41  # Factorizations                       : 12
% 0.19/0.41  # Equation resolutions                 : 26
% 0.19/0.41  # Propositional unsat checks           : 0
% 0.19/0.41  #    Propositional check models        : 0
% 0.19/0.41  #    Propositional check unsatisfiable : 0
% 0.19/0.41  #    Propositional clauses             : 0
% 0.19/0.41  #    Propositional clauses after purity: 0
% 0.19/0.41  #    Propositional unsat core size     : 0
% 0.19/0.41  #    Propositional preprocessing time  : 0.000
% 0.19/0.41  #    Propositional encoding time       : 0.000
% 0.19/0.41  #    Propositional solver time         : 0.000
% 0.19/0.41  #    Success case prop preproc time    : 0.000
% 0.19/0.41  #    Success case prop encoding time   : 0.000
% 0.19/0.41  #    Success case prop solver time     : 0.000
% 0.19/0.41  # Current number of processed clauses  : 182
% 0.19/0.41  #    Positive orientable unit clauses  : 28
% 0.19/0.41  #    Positive unorientable unit clauses: 0
% 0.19/0.41  #    Negative unit clauses             : 3
% 0.19/0.41  #    Non-unit-clauses                  : 151
% 0.19/0.41  # Current number of unprocessed clauses: 372
% 0.19/0.41  # ...number of literals in the above   : 1520
% 0.19/0.41  # Current number of archived formulas  : 0
% 0.19/0.41  # Current number of archived clauses   : 70
% 0.19/0.41  # Clause-clause subsumption calls (NU) : 4456
% 0.19/0.41  # Rec. Clause-clause subsumption calls : 1753
% 0.19/0.41  # Non-unit clause-clause subsumptions  : 63
% 0.19/0.41  # Unit Clause-clause subsumption calls : 90
% 0.19/0.41  # Rewrite failures with RHS unbound    : 0
% 0.19/0.41  # BW rewrite match attempts            : 8
% 0.19/0.41  # BW rewrite match successes           : 4
% 0.19/0.41  # Condensation attempts                : 0
% 0.19/0.41  # Condensation successes               : 0
% 0.19/0.41  # Termbank termtop insertions          : 33707
% 0.19/0.41  
% 0.19/0.41  # -------------------------------------------------
% 0.19/0.41  # User time                : 0.063 s
% 0.19/0.41  # System time              : 0.004 s
% 0.19/0.41  # Total time               : 0.068 s
% 0.19/0.41  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
