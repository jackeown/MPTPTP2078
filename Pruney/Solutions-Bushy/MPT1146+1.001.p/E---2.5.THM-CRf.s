%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1146+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:40:49 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  171 (1130673 expanded)
%              Number of clauses        :  138 (446221 expanded)
%              Number of leaves         :   16 (265332 expanded)
%              Depth                    :   42
%              Number of atoms          :  694 (15342424 expanded)
%              Number of equality atoms :   47 (247502 expanded)
%              Maximal formula depth    :   22 (   4 average)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

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

fof(dt_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(redefinition_r3_orders_2,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v2_struct_0(X1)
        & v3_orders_2(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( r3_orders_2(X1,X2,X3)
      <=> r1_orders_2(X1,X2,X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(cc4_relset_1,axiom,(
    ! [X1,X2] :
      ( v1_xboole_0(X1)
     => ! [X3] :
          ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
         => v1_xboole_0(X3) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_orders_2)).

fof(d2_tarski,axiom,(
    ! [X1,X2,X3] :
      ( X3 = k2_tarski(X1,X2)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X4 = X1
            | X4 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(fc1_struct_0,axiom,(
    ! [X1] :
      ( ( v2_struct_0(X1)
        & l1_struct_0(X1) )
     => v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_relat_2)).

fof(cc1_relset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => v1_relat_1(X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(d11_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v6_orders_2(X2,X1)
          <=> r7_relat_2(u1_orders_2(X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d11_orders_2)).

fof(commutativity_k2_tarski,axiom,(
    ! [X1,X2] : k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(c_0_16,negated_conjecture,(
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

fof(c_0_17,plain,(
    ! [X49,X50] :
      ( ~ r2_hidden(X49,X50)
      | ~ v1_xboole_0(X50) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

fof(c_0_18,plain,(
    ! [X31,X32,X33] :
      ( ( ~ r1_orders_2(X31,X32,X33)
        | r2_hidden(k4_tarski(X32,X33),u1_orders_2(X31))
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) )
      & ( ~ r2_hidden(k4_tarski(X32,X33),u1_orders_2(X31))
        | r1_orders_2(X31,X32,X33)
        | ~ m1_subset_1(X33,u1_struct_0(X31))
        | ~ m1_subset_1(X32,u1_struct_0(X31))
        | ~ l1_orders_2(X31) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

fof(c_0_19,plain,(
    ! [X34,X35,X36] :
      ( v1_xboole_0(X34)
      | ~ m1_subset_1(X35,X34)
      | ~ m1_subset_1(X36,X34)
      | m1_subset_1(k7_domain_1(X34,X35,X36),k1_zfmisc_1(X34)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_domain_1])])])).

fof(c_0_20,negated_conjecture,(
    ! [X55] :
      ( v3_orders_2(esk4_0)
      & l1_orders_2(esk4_0)
      & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
      & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
      & ( r1_orders_2(esk4_0,esk5_0,esk6_0)
        | r1_orders_2(esk4_0,esk6_0,esk5_0)
        | v6_orders_2(esk7_0,esk4_0) )
      & ( ~ v6_orders_2(X55,esk4_0)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ r2_hidden(esk5_0,X55)
        | ~ r2_hidden(esk6_0,X55)
        | v6_orders_2(esk7_0,esk4_0) )
      & ( r1_orders_2(esk4_0,esk5_0,esk6_0)
        | r1_orders_2(esk4_0,esk6_0,esk5_0)
        | m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) )
      & ( ~ v6_orders_2(X55,esk4_0)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ r2_hidden(esk5_0,X55)
        | ~ r2_hidden(esk6_0,X55)
        | m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) )
      & ( r1_orders_2(esk4_0,esk5_0,esk6_0)
        | r1_orders_2(esk4_0,esk6_0,esk5_0)
        | r2_hidden(esk5_0,esk7_0) )
      & ( ~ v6_orders_2(X55,esk4_0)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ r2_hidden(esk5_0,X55)
        | ~ r2_hidden(esk6_0,X55)
        | r2_hidden(esk5_0,esk7_0) )
      & ( r1_orders_2(esk4_0,esk5_0,esk6_0)
        | r1_orders_2(esk4_0,esk6_0,esk5_0)
        | r2_hidden(esk6_0,esk7_0) )
      & ( ~ v6_orders_2(X55,esk4_0)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ r2_hidden(esk5_0,X55)
        | ~ r2_hidden(esk6_0,X55)
        | r2_hidden(esk6_0,esk7_0) )
      & ( r1_orders_2(esk4_0,esk5_0,esk6_0)
        | r1_orders_2(esk4_0,esk6_0,esk5_0)
        | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) )
      & ( ~ v6_orders_2(X55,esk4_0)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ r2_hidden(esk5_0,X55)
        | ~ r2_hidden(esk6_0,X55)
        | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) )
      & ( r1_orders_2(esk4_0,esk5_0,esk6_0)
        | r1_orders_2(esk4_0,esk6_0,esk5_0)
        | ~ r1_orders_2(esk4_0,esk6_0,esk5_0) )
      & ( ~ v6_orders_2(X55,esk4_0)
        | ~ m1_subset_1(X55,k1_zfmisc_1(u1_struct_0(esk4_0)))
        | ~ r2_hidden(esk5_0,X55)
        | ~ r2_hidden(esk6_0,X55)
        | ~ r1_orders_2(esk4_0,esk6_0,esk5_0) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_16])])])])])])).

fof(c_0_21,plain,(
    ! [X43,X44,X45] :
      ( ( ~ r3_orders_2(X43,X44,X45)
        | r1_orders_2(X43,X44,X45)
        | v2_struct_0(X43)
        | ~ v3_orders_2(X43)
        | ~ l1_orders_2(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X43)) )
      & ( ~ r1_orders_2(X43,X44,X45)
        | r3_orders_2(X43,X44,X45)
        | v2_struct_0(X43)
        | ~ v3_orders_2(X43)
        | ~ l1_orders_2(X43)
        | ~ m1_subset_1(X44,u1_struct_0(X43))
        | ~ m1_subset_1(X45,u1_struct_0(X43)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_r3_orders_2])])])])).

cnf(c_0_22,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_23,plain,
    ( r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1))
    | ~ r1_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_24,plain,(
    ! [X8,X9,X10] :
      ( ~ v1_xboole_0(X8)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X9,X8)))
      | v1_xboole_0(X10) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc4_relset_1])])])).

fof(c_0_25,plain,(
    ! [X38] :
      ( ~ l1_orders_2(X38)
      | m1_subset_1(u1_orders_2(X38),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X38),u1_struct_0(X38)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_26,plain,(
    ! [X40,X41,X42] :
      ( v1_xboole_0(X40)
      | ~ m1_subset_1(X41,X40)
      | ~ m1_subset_1(X42,X40)
      | k7_domain_1(X40,X41,X42) = k2_tarski(X41,X42) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

cnf(c_0_27,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_28,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_29,plain,(
    ! [X46,X47,X48] :
      ( ( ~ v6_orders_2(k7_domain_1(u1_struct_0(X46),X47,X48),X46)
        | ~ m1_subset_1(k7_domain_1(u1_struct_0(X46),X47,X48),k1_zfmisc_1(u1_struct_0(X46)))
        | r3_orders_2(X46,X47,X48)
        | r3_orders_2(X46,X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ l1_orders_2(X46) )
      & ( v6_orders_2(k7_domain_1(u1_struct_0(X46),X47,X48),X46)
        | ~ r3_orders_2(X46,X47,X48)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ l1_orders_2(X46) )
      & ( m1_subset_1(k7_domain_1(u1_struct_0(X46),X47,X48),k1_zfmisc_1(u1_struct_0(X46)))
        | ~ r3_orders_2(X46,X47,X48)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ l1_orders_2(X46) )
      & ( v6_orders_2(k7_domain_1(u1_struct_0(X46),X47,X48),X46)
        | ~ r3_orders_2(X46,X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ l1_orders_2(X46) )
      & ( m1_subset_1(k7_domain_1(u1_struct_0(X46),X47,X48),k1_zfmisc_1(u1_struct_0(X46)))
        | ~ r3_orders_2(X46,X48,X47)
        | ~ m1_subset_1(X48,u1_struct_0(X46))
        | ~ m1_subset_1(X47,u1_struct_0(X46))
        | v2_struct_0(X46)
        | ~ v3_orders_2(X46)
        | ~ l1_orders_2(X46) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_orders_2])])])])])).

cnf(c_0_30,plain,
    ( r3_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_31,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_32,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_33,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_34,plain,
    ( ~ r1_orders_2(X1,X2,X3)
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(u1_orders_2(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_35,plain,
    ( v1_xboole_0(X2)
    | ~ v1_xboole_0(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_36,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_37,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_38,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),X1,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_39,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(X1),X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_40,negated_conjecture,
    ( r3_orders_2(esk4_0,X1,esk5_0)
    | v2_struct_0(esk4_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_41,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_42,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ v1_xboole_0(u1_orders_2(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_31]),c_0_33])])).

cnf(c_0_43,plain,
    ( v1_xboole_0(u1_orders_2(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

cnf(c_0_44,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),X1,esk6_0) = k2_tarski(X1,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_28])).

fof(c_0_45,plain,(
    ! [X15,X16,X17,X18,X19,X20,X21,X22] :
      ( ( ~ r2_hidden(X18,X17)
        | X18 = X15
        | X18 = X16
        | X17 != k2_tarski(X15,X16) )
      & ( X19 != X15
        | r2_hidden(X19,X17)
        | X17 != k2_tarski(X15,X16) )
      & ( X19 != X16
        | r2_hidden(X19,X17)
        | X17 != k2_tarski(X15,X16) )
      & ( esk1_3(X20,X21,X22) != X20
        | ~ r2_hidden(esk1_3(X20,X21,X22),X22)
        | X22 = k2_tarski(X20,X21) )
      & ( esk1_3(X20,X21,X22) != X21
        | ~ r2_hidden(esk1_3(X20,X21,X22),X22)
        | X22 = k2_tarski(X20,X21) )
      & ( r2_hidden(esk1_3(X20,X21,X22),X22)
        | esk1_3(X20,X21,X22) = X20
        | esk1_3(X20,X21,X22) = X21
        | X22 = k2_tarski(X20,X21) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d2_tarski])])])])])])).

cnf(c_0_46,negated_conjecture,
    ( ~ v6_orders_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(esk5_0,X1)
    | ~ r2_hidden(esk6_0,X1)
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_47,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | m1_subset_1(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(spm,[status(thm)],[c_0_38,c_0_31])).

cnf(c_0_48,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),X1,esk6_0),esk4_0)
    | ~ r3_orders_2(esk4_0,esk6_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_28]),c_0_32]),c_0_33])])).

cnf(c_0_49,negated_conjecture,
    ( r3_orders_2(esk4_0,esk6_0,esk5_0)
    | v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_28])])).

cnf(c_0_50,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_42,c_0_43]),c_0_33])])).

cnf(c_0_51,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_31])).

cnf(c_0_52,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X2,X4) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_53,plain,
    ( r2_hidden(X1,X3)
    | X1 != X2
    | X3 != k2_tarski(X4,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

fof(c_0_54,plain,(
    ! [X39] :
      ( ~ v2_struct_0(X39)
      | ~ l1_struct_0(X39)
      | v1_xboole_0(u1_struct_0(X39)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc1_struct_0])])).

fof(c_0_55,plain,(
    ! [X37] :
      ( ~ l1_orders_2(X37)
      | l1_struct_0(X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_56,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
    | ~ r2_hidden(esk5_0,k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0))
    | ~ r2_hidden(esk6_0,k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_47])).

cnf(c_0_57,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk7_0)
    | v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_31])])).

cnf(c_0_58,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_51])).

cnf(c_0_59,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X1,X3) ),
    inference(er,[status(thm)],[c_0_52])).

cnf(c_0_60,plain,
    ( r2_hidden(X1,X2)
    | X2 != k2_tarski(X3,X1) ),
    inference(er,[status(thm)],[c_0_53])).

cnf(c_0_61,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_62,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_63,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r2_hidden(esk5_0,k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0))
    | ~ r2_hidden(esk6_0,k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_57]),c_0_41])).

cnf(c_0_64,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_41]),c_0_28])])).

cnf(c_0_65,plain,
    ( r2_hidden(X1,k2_tarski(X1,X2)) ),
    inference(er,[status(thm)],[c_0_59])).

cnf(c_0_66,plain,
    ( r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(er,[status(thm)],[c_0_60])).

cnf(c_0_67,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | ~ v2_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_68,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ v1_xboole_0(u1_orders_2(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_28]),c_0_33])])).

cnf(c_0_69,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_65]),c_0_66])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_67]),c_0_33])])).

cnf(c_0_71,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_68,c_0_43]),c_0_33])])).

cnf(c_0_72,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk7_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_69]),c_0_70])).

cnf(c_0_73,negated_conjecture,
    ( ~ v6_orders_2(X1,esk4_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk4_0)))
    | ~ r2_hidden(esk5_0,X1)
    | ~ r2_hidden(esk6_0,X1)
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_74,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0)
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_71,c_0_51])).

cnf(c_0_75,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_41]),c_0_28])])).

cnf(c_0_76,negated_conjecture,
    ( r3_orders_2(esk4_0,X1,esk6_0)
    | v2_struct_0(esk4_0)
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_30,c_0_28]),c_0_32]),c_0_33])])).

cnf(c_0_77,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r2_hidden(esk5_0,k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0))
    | ~ r2_hidden(esk6_0,k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0),esk4_0) ),
    inference(spm,[status(thm)],[c_0_73,c_0_47])).

cnf(c_0_78,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_75]),c_0_31])])).

cnf(c_0_79,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(X1),X2,X3),X1)
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X2,X3)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_80,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(esk4_0)
    | r2_hidden(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_75]),c_0_31])])).

cnf(c_0_81,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_78]),c_0_65]),c_0_66])]),c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r2_hidden(esk5_0,esk7_0)
    | v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_78]),c_0_32]),c_0_33]),c_0_28]),c_0_31])]),c_0_80])).

fof(c_0_83,plain,(
    ! [X24,X25,X26,X27,X28] :
      ( ( ~ r7_relat_2(X24,X25)
        | ~ r2_hidden(X26,X25)
        | ~ r2_hidden(X27,X25)
        | r2_hidden(k4_tarski(X26,X27),X24)
        | r2_hidden(k4_tarski(X27,X26),X24)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk2_2(X24,X28),X28)
        | r7_relat_2(X24,X28)
        | ~ v1_relat_1(X24) )
      & ( r2_hidden(esk3_2(X24,X28),X28)
        | r7_relat_2(X24,X28)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(esk2_2(X24,X28),esk3_2(X24,X28)),X24)
        | r7_relat_2(X24,X28)
        | ~ v1_relat_1(X24) )
      & ( ~ r2_hidden(k4_tarski(esk3_2(X24,X28),esk2_2(X24,X28)),X24)
        | r7_relat_2(X24,X28)
        | ~ v1_relat_1(X24) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d7_relat_2])])])])])])])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r2_hidden(esk5_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_85,negated_conjecture,
    ( ~ v2_struct_0(esk4_0)
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_67]),c_0_33])])).

cnf(c_0_86,plain,
    ( r2_hidden(k4_tarski(X3,X4),X1)
    | r2_hidden(k4_tarski(X4,X3),X1)
    | ~ r7_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ r2_hidden(X4,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0)
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_84]),c_0_85])).

fof(c_0_88,plain,(
    ! [X5,X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
      | v1_relat_1(X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc1_relset_1])])).

cnf(c_0_89,plain,
    ( r2_hidden(k4_tarski(X1,X1),X2)
    | ~ r2_hidden(X1,X3)
    | ~ r7_relat_2(X2,X3)
    | ~ v1_relat_1(X2) ),
    inference(ef,[status(thm)],[c_0_86])).

cnf(c_0_90,negated_conjecture,
    ( r2_hidden(esk5_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_75]),c_0_31])])).

cnf(c_0_91,plain,
    ( v1_relat_1(X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(split_conjunct,[status(thm)],[c_0_88])).

cnf(c_0_92,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_93,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk5_0),X1)
    | ~ r7_relat_2(X1,esk7_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_89,c_0_90])).

cnf(c_0_94,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_91,c_0_36])).

fof(c_0_95,plain,(
    ! [X13,X14] :
      ( ( ~ v6_orders_2(X14,X13)
        | r7_relat_2(u1_orders_2(X13),X14)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) )
      & ( ~ r7_relat_2(u1_orders_2(X13),X14)
        | v6_orders_2(X14,X13)
        | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(X13)))
        | ~ l1_orders_2(X13) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d11_orders_2])])])])).

cnf(c_0_96,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r2_hidden(esk6_0,esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_97,negated_conjecture,
    ( r1_orders_2(X1,esk5_0,esk5_0)
    | ~ r7_relat_2(u1_orders_2(X1),esk7_0)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(esk5_0,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_93]),c_0_94])).

cnf(c_0_98,plain,
    ( r7_relat_2(u1_orders_2(X2),X1)
    | ~ v6_orders_2(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_99,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_96]),c_0_28])])).

cnf(c_0_100,negated_conjecture,
    ( r3_orders_2(esk4_0,esk6_0,esk5_0)
    | v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_96]),c_0_28])])).

cnf(c_0_101,negated_conjecture,
    ( r1_orders_2(X1,esk5_0,esk5_0)
    | ~ v6_orders_2(esk7_0,X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(esk5_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_97,c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_103,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | v6_orders_2(esk7_0,esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_104,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_99]),c_0_65]),c_0_66])]),c_0_96])).

cnf(c_0_105,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,esk7_0)
    | v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_99]),c_0_32]),c_0_33]),c_0_28]),c_0_31])]),c_0_100])).

cnf(c_0_106,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_101,c_0_102]),c_0_33]),c_0_31])]),c_0_103])).

cnf(c_0_107,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_104,c_0_105])).

cnf(c_0_108,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk5_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_106]),c_0_28])])).

cnf(c_0_109,negated_conjecture,
    ( r3_orders_2(esk4_0,esk6_0,esk5_0)
    | v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_106]),c_0_28])])).

cnf(c_0_110,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,esk7_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_107]),c_0_70])).

cnf(c_0_111,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_56,c_0_108]),c_0_65]),c_0_66])]),c_0_106])).

cnf(c_0_112,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk5_0,esk5_0)
    | v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_108]),c_0_32]),c_0_33]),c_0_28]),c_0_31])]),c_0_109])).

cnf(c_0_113,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r2_hidden(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_110,c_0_96]),c_0_28])])).

cnf(c_0_114,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_111,c_0_112])).

cnf(c_0_115,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0)
    | r2_hidden(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_113]),c_0_31])])).

cnf(c_0_116,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(esk4_0)
    | r2_hidden(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_113]),c_0_31])])).

cnf(c_0_117,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk5_0,esk5_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_114]),c_0_70])).

cnf(c_0_118,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_115]),c_0_65]),c_0_66])]),c_0_113])).

cnf(c_0_119,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r2_hidden(esk6_0,esk7_0)
    | v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_115]),c_0_32]),c_0_33]),c_0_28]),c_0_31])]),c_0_116])).

cnf(c_0_120,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_117,c_0_106]),c_0_28])])).

cnf(c_0_121,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r2_hidden(esk6_0,esk7_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_118,c_0_119])).

cnf(c_0_122,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_120]),c_0_31])])).

cnf(c_0_123,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_120]),c_0_31])])).

cnf(c_0_124,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0)
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_121]),c_0_85])).

cnf(c_0_125,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_122]),c_0_65]),c_0_66])]),c_0_120])).

cnf(c_0_126,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk5_0)
    | v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_122]),c_0_32]),c_0_33]),c_0_28]),c_0_31])]),c_0_123])).

cnf(c_0_127,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,X1),X2)
    | r2_hidden(k4_tarski(X1,esk5_0),X2)
    | ~ r2_hidden(X1,esk7_0)
    | ~ r7_relat_2(X2,esk7_0)
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_86,c_0_90])).

cnf(c_0_128,negated_conjecture,
    ( r2_hidden(esk6_0,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_124,c_0_113]),c_0_31])])).

cnf(c_0_129,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),X1,esk5_0) = k2_tarski(X1,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_31])).

cnf(c_0_130,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_125,c_0_126])).

cnf(c_0_131,negated_conjecture,
    ( r2_hidden(k4_tarski(esk6_0,esk5_0),X1)
    | r2_hidden(k4_tarski(esk5_0,esk6_0),X1)
    | ~ r7_relat_2(X1,esk7_0)
    | ~ v1_relat_1(X1) ),
    inference(spm,[status(thm)],[c_0_127,c_0_128])).

cnf(c_0_132,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk5_0) = k2_tarski(esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_129,c_0_31])).

cnf(c_0_133,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk5_0)
    | ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_130]),c_0_85])).

cnf(c_0_134,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk6_0),u1_orders_2(X1))
    | r2_hidden(k4_tarski(esk6_0,esk5_0),u1_orders_2(X1))
    | ~ v6_orders_2(esk7_0,X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_131,c_0_98]),c_0_94])).

fof(c_0_135,plain,(
    ! [X11,X12] : k2_tarski(X11,X12) = k2_tarski(X12,X11) ),
    inference(variable_rename,[status(thm)],[commutativity_k2_tarski])).

cnf(c_0_136,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk5_0) = k2_tarski(esk5_0,esk5_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_132])).

cnf(c_0_137,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_133,c_0_120]),c_0_31])])).

cnf(c_0_138,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r2_hidden(k4_tarski(esk6_0,esk5_0),u1_orders_2(esk4_0))
    | r2_hidden(k4_tarski(esk5_0,esk6_0),u1_orders_2(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_134,c_0_102]),c_0_33])]),c_0_103])).

cnf(c_0_139,plain,
    ( k2_tarski(X1,X2) = k2_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_135])).

cnf(c_0_140,plain,
    ( r2_hidden(k4_tarski(X1,X1),X2)
    | ~ r7_relat_2(X2,k2_tarski(X3,X1))
    | ~ v1_relat_1(X2) ),
    inference(spm,[status(thm)],[c_0_89,c_0_66])).

cnf(c_0_141,plain,
    ( m1_subset_1(k7_domain_1(u1_struct_0(X1),X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ r3_orders_2(X1,X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_142,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk5_0) = k2_tarski(esk5_0,esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_136,c_0_137]),c_0_31])])).

cnf(c_0_143,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,esk5_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_137]),c_0_31])])).

cnf(c_0_144,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r2_hidden(k4_tarski(esk5_0,esk6_0),u1_orders_2(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_138]),c_0_33]),c_0_31]),c_0_28])])).

cnf(c_0_145,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk6_0,esk5_0) = k2_tarski(esk5_0,esk6_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_129,c_0_28]),c_0_139])).

cnf(c_0_146,plain,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(X2))
    | ~ v6_orders_2(k2_tarski(X3,X1),X2)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(k2_tarski(X3,X1),k1_zfmisc_1(u1_struct_0(X2))) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_140,c_0_98]),c_0_94])).

cnf(c_0_147,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | m1_subset_1(k2_tarski(esk5_0,esk5_0),k1_zfmisc_1(u1_struct_0(esk4_0))) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_141,c_0_142]),c_0_32]),c_0_33]),c_0_31])]),c_0_143])).

cnf(c_0_148,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | v6_orders_2(k2_tarski(esk5_0,esk5_0),esk4_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_142]),c_0_32]),c_0_33]),c_0_31])]),c_0_143])).

cnf(c_0_149,negated_conjecture,
    ( r1_orders_2(esk4_0,esk6_0,esk5_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_92,c_0_144]),c_0_33]),c_0_28]),c_0_31])])).

cnf(c_0_150,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk6_0,esk5_0) = k2_tarski(esk5_0,esk6_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_145])).

cnf(c_0_151,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r2_hidden(k4_tarski(esk5_0,esk5_0),u1_orders_2(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_146,c_0_147]),c_0_33])]),c_0_148])).

cnf(c_0_152,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk5_0,esk6_0) = k2_tarski(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_137]),c_0_31])])).

cnf(c_0_153,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),X1,esk5_0),esk4_0)
    | ~ r3_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_31]),c_0_32]),c_0_33])])).

cnf(c_0_154,negated_conjecture,
    ( r3_orders_2(esk4_0,esk6_0,esk5_0)
    | v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_149]),c_0_28])])).

cnf(c_0_155,negated_conjecture,
    ( k7_domain_1(u1_struct_0(esk4_0),esk6_0,esk5_0) = k2_tarski(esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_150,c_0_137]),c_0_31])])).

cnf(c_0_156,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | ~ v1_xboole_0(u1_orders_2(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_22,c_0_151])).

cnf(c_0_157,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk4_0,esk6_0,esk5_0)
    | ~ v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_56,c_0_152]),c_0_65]),c_0_152]),c_0_66]),c_0_152])])).

cnf(c_0_158,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0)
    | v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_153,c_0_154]),c_0_155]),c_0_28])])).

cnf(c_0_159,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | ~ v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_156,c_0_43]),c_0_33])])).

cnf(c_0_160,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_157,c_0_158]),c_0_149]),c_0_159])).

cnf(c_0_161,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ r1_orders_2(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_70,c_0_160])).

cnf(c_0_162,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_161,c_0_149]),c_0_28])])).

cnf(c_0_163,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk4_0,esk5_0,esk6_0)
    | ~ v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_77,c_0_152]),c_0_65]),c_0_152]),c_0_66]),c_0_152])])).

cnf(c_0_164,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | v6_orders_2(k7_domain_1(u1_struct_0(esk4_0),X1,esk6_0),esk4_0)
    | ~ r3_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_28]),c_0_32]),c_0_33])])).

cnf(c_0_165,negated_conjecture,
    ( r3_orders_2(esk4_0,esk5_0,esk6_0)
    | v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_162]),c_0_31])])).

cnf(c_0_166,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0))
    | ~ v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_163,c_0_162])])).

cnf(c_0_167,negated_conjecture,
    ( v2_struct_0(esk4_0)
    | v6_orders_2(k2_tarski(esk5_0,esk6_0),esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_164,c_0_165]),c_0_152]),c_0_31])])).

cnf(c_0_168,negated_conjecture,
    ( v2_struct_0(esk4_0) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_166,c_0_167]),c_0_159])).

cnf(c_0_169,negated_conjecture,
    ( ~ r1_orders_2(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_85,c_0_168])])).

cnf(c_0_170,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_169,c_0_162]),c_0_31])]),
    [proof]).

%------------------------------------------------------------------------------
