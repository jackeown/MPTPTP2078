%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:14:55 EST 2020

% Result     : Theorem 0.47s
% Output     : CNFRefutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 562 expanded)
%              Number of clauses        :   57 ( 199 expanded)
%              Number of leaves         :   18 ( 135 expanded)
%              Depth                    :   13
%              Number of atoms          :  489 (3234 expanded)
%              Number of equality atoms :   47 ( 359 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   74 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t18_lattice3,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3)) = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattice3)).

fof(d4_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v3_orders_2(X1)
      <=> r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_orders_2)).

fof(d1_relat_2,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( r1_relat_2(X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
             => r2_hidden(k4_tarski(X3,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_2)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(dt_u1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(dt_k10_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k10_lattice3)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(redefinition_k13_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k13_lattice3)).

fof(commutativity_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k12_lattice3)).

fof(redefinition_k12_lattice3,axiom,(
    ! [X1,X2,X3] :
      ( ( v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1)
        & m1_subset_1(X2,u1_struct_0(X1))
        & m1_subset_1(X3,u1_struct_0(X1)) )
     => k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(l28_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v2_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k11_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X4,X2)
                      & r1_orders_2(X1,X4,X3)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X5,X2)
                              & r1_orders_2(X1,X5,X3) )
                           => r1_orders_2(X1,X5,X4) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(cc2_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v2_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(d9_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( r1_orders_2(X1,X2,X3)
              <=> r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(l26_lattice3,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X1))
                 => ( X4 = k10_lattice3(X1,X2,X3)
                  <=> ( r1_orders_2(X1,X2,X4)
                      & r1_orders_2(X1,X3,X4)
                      & ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X1))
                         => ( ( r1_orders_2(X1,X2,X5)
                              & r1_orders_2(X1,X3,X5) )
                           => r1_orders_2(X1,X4,X5) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l26_lattice3)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattice3)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(c_0_18,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & v2_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3)) = X2 ) ) ) ),
    inference(assume_negation,[status(cth)],[t18_lattice3])).

fof(c_0_19,plain,(
    ! [X18] :
      ( ( ~ v3_orders_2(X18)
        | r1_relat_2(u1_orders_2(X18),u1_struct_0(X18))
        | ~ l1_orders_2(X18) )
      & ( ~ r1_relat_2(u1_orders_2(X18),u1_struct_0(X18))
        | v3_orders_2(X18)
        | ~ l1_orders_2(X18) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).

fof(c_0_20,negated_conjecture,
    ( v3_orders_2(esk4_0)
    & v5_orders_2(esk4_0)
    & v1_lattice3(esk4_0)
    & v2_lattice3(esk4_0)
    & l1_orders_2(esk4_0)
    & m1_subset_1(esk5_0,u1_struct_0(esk4_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk4_0))
    & k12_lattice3(esk4_0,esk5_0,k13_lattice3(esk4_0,esk5_0,esk6_0)) != esk5_0 ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).

fof(c_0_21,plain,(
    ! [X12,X13,X14,X15] :
      ( ( ~ r1_relat_2(X12,X13)
        | ~ r2_hidden(X14,X13)
        | r2_hidden(k4_tarski(X14,X14),X12)
        | ~ v1_relat_1(X12) )
      & ( r2_hidden(esk1_2(X12,X15),X15)
        | r1_relat_2(X12,X15)
        | ~ v1_relat_1(X12) )
      & ( ~ r2_hidden(k4_tarski(esk1_2(X12,X15),esk1_2(X12,X15)),X12)
        | r1_relat_2(X12,X15)
        | ~ v1_relat_1(X12) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).

cnf(c_0_22,plain,
    ( r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))
    | ~ v3_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_23,negated_conjecture,
    ( v3_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_24,negated_conjecture,
    ( l1_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_25,plain,(
    ! [X8,X9] :
      ( ~ v1_relat_1(X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X8))
      | v1_relat_1(X9) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_26,plain,(
    ! [X23] :
      ( ~ l1_orders_2(X23)
      | m1_subset_1(u1_orders_2(X23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23)))) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).

fof(c_0_27,plain,(
    ! [X10,X11] : v1_relat_1(k2_zfmisc_1(X10,X11)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_28,plain,(
    ! [X29,X30,X31] :
      ( ~ l1_orders_2(X29)
      | ~ m1_subset_1(X30,u1_struct_0(X29))
      | ~ m1_subset_1(X31,u1_struct_0(X29))
      | m1_subset_1(k10_lattice3(X29,X30,X31),u1_struct_0(X29)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).

cnf(c_0_29,plain,
    ( r2_hidden(k4_tarski(X3,X3),X1)
    | ~ r1_relat_2(X1,X2)
    | ~ r2_hidden(X3,X2)
    | ~ v1_relat_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_30,negated_conjecture,
    ( r1_relat_2(u1_orders_2(esk4_0),u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22,c_0_23]),c_0_24])])).

cnf(c_0_31,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,plain,
    ( m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

cnf(c_0_33,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

fof(c_0_34,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,X7)
      | v1_xboole_0(X7)
      | r2_hidden(X6,X7) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_35,plain,(
    ! [X47,X48,X49] :
      ( ~ v5_orders_2(X47)
      | ~ v1_lattice3(X47)
      | ~ l1_orders_2(X47)
      | ~ m1_subset_1(X48,u1_struct_0(X47))
      | ~ m1_subset_1(X49,u1_struct_0(X47))
      | k13_lattice3(X47,X48,X49) = k10_lattice3(X47,X48,X49) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).

fof(c_0_36,plain,(
    ! [X26,X27,X28] :
      ( ~ v5_orders_2(X26)
      | ~ v2_lattice3(X26)
      | ~ l1_orders_2(X26)
      | ~ m1_subset_1(X27,u1_struct_0(X26))
      | ~ m1_subset_1(X28,u1_struct_0(X26))
      | k12_lattice3(X26,X27,X28) = k12_lattice3(X26,X28,X27) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k12_lattice3])])).

cnf(c_0_37,plain,
    ( m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_38,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_39,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk4_0))
    | ~ v1_relat_1(u1_orders_2(esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_29,c_0_30])).

cnf(c_0_40,plain,
    ( v1_relat_1(u1_orders_2(X1))
    | ~ l1_orders_2(X1) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk4_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_43,plain,
    ( k13_lattice3(X1,X2,X3) = k10_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,negated_conjecture,
    ( v5_orders_2(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_45,negated_conjecture,
    ( v1_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

fof(c_0_46,plain,(
    ! [X44,X45,X46] :
      ( ~ v5_orders_2(X44)
      | ~ v2_lattice3(X44)
      | ~ l1_orders_2(X44)
      | ~ m1_subset_1(X45,u1_struct_0(X44))
      | ~ m1_subset_1(X46,u1_struct_0(X44))
      | k12_lattice3(X44,X45,X46) = k11_lattice3(X44,X45,X46) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).

cnf(c_0_47,plain,
    ( k12_lattice3(X1,X2,X3) = k12_lattice3(X1,X3,X2)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_48,negated_conjecture,
    ( v2_lattice3(esk4_0) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_49,negated_conjecture,
    ( m1_subset_1(k10_lattice3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37,c_0_38]),c_0_24])])).

fof(c_0_50,plain,(
    ! [X38,X39,X40,X41,X42] :
      ( ( r1_orders_2(X38,X41,X39)
        | X41 != k11_lattice3(X38,X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v5_orders_2(X38)
        | ~ v2_lattice3(X38)
        | ~ l1_orders_2(X38) )
      & ( r1_orders_2(X38,X41,X40)
        | X41 != k11_lattice3(X38,X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v5_orders_2(X38)
        | ~ v2_lattice3(X38)
        | ~ l1_orders_2(X38) )
      & ( ~ m1_subset_1(X42,u1_struct_0(X38))
        | ~ r1_orders_2(X38,X42,X39)
        | ~ r1_orders_2(X38,X42,X40)
        | r1_orders_2(X38,X42,X41)
        | X41 != k11_lattice3(X38,X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v5_orders_2(X38)
        | ~ v2_lattice3(X38)
        | ~ l1_orders_2(X38) )
      & ( m1_subset_1(esk3_4(X38,X39,X40,X41),u1_struct_0(X38))
        | ~ r1_orders_2(X38,X41,X39)
        | ~ r1_orders_2(X38,X41,X40)
        | X41 = k11_lattice3(X38,X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v5_orders_2(X38)
        | ~ v2_lattice3(X38)
        | ~ l1_orders_2(X38) )
      & ( r1_orders_2(X38,esk3_4(X38,X39,X40,X41),X39)
        | ~ r1_orders_2(X38,X41,X39)
        | ~ r1_orders_2(X38,X41,X40)
        | X41 = k11_lattice3(X38,X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v5_orders_2(X38)
        | ~ v2_lattice3(X38)
        | ~ l1_orders_2(X38) )
      & ( r1_orders_2(X38,esk3_4(X38,X39,X40,X41),X40)
        | ~ r1_orders_2(X38,X41,X39)
        | ~ r1_orders_2(X38,X41,X40)
        | X41 = k11_lattice3(X38,X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v5_orders_2(X38)
        | ~ v2_lattice3(X38)
        | ~ l1_orders_2(X38) )
      & ( ~ r1_orders_2(X38,esk3_4(X38,X39,X40,X41),X41)
        | ~ r1_orders_2(X38,X41,X39)
        | ~ r1_orders_2(X38,X41,X40)
        | X41 = k11_lattice3(X38,X39,X40)
        | ~ m1_subset_1(X41,u1_struct_0(X38))
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ m1_subset_1(X39,u1_struct_0(X38))
        | v2_struct_0(X38)
        | ~ v5_orders_2(X38)
        | ~ v2_lattice3(X38)
        | ~ l1_orders_2(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).

fof(c_0_51,plain,(
    ! [X25] :
      ( ~ l1_orders_2(X25)
      | ~ v2_lattice3(X25)
      | ~ v2_struct_0(X25) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).

fof(c_0_52,plain,(
    ! [X19,X20,X21] :
      ( ( ~ r1_orders_2(X19,X20,X21)
        | r2_hidden(k4_tarski(X20,X21),u1_orders_2(X19))
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ l1_orders_2(X19) )
      & ( ~ r2_hidden(k4_tarski(X20,X21),u1_orders_2(X19))
        | r1_orders_2(X19,X20,X21)
        | ~ m1_subset_1(X21,u1_struct_0(X19))
        | ~ m1_subset_1(X20,u1_struct_0(X19))
        | ~ l1_orders_2(X19) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).

cnf(c_0_53,negated_conjecture,
    ( r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk4_0))
    | ~ r2_hidden(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_40]),c_0_24])])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk5_0,u1_struct_0(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

fof(c_0_55,plain,(
    ! [X32,X33,X34,X35,X36] :
      ( ( r1_orders_2(X32,X33,X35)
        | X35 != k10_lattice3(X32,X33,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v1_lattice3(X32)
        | ~ l1_orders_2(X32) )
      & ( r1_orders_2(X32,X34,X35)
        | X35 != k10_lattice3(X32,X33,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v1_lattice3(X32)
        | ~ l1_orders_2(X32) )
      & ( ~ m1_subset_1(X36,u1_struct_0(X32))
        | ~ r1_orders_2(X32,X33,X36)
        | ~ r1_orders_2(X32,X34,X36)
        | r1_orders_2(X32,X35,X36)
        | X35 != k10_lattice3(X32,X33,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v1_lattice3(X32)
        | ~ l1_orders_2(X32) )
      & ( m1_subset_1(esk2_4(X32,X33,X34,X35),u1_struct_0(X32))
        | ~ r1_orders_2(X32,X33,X35)
        | ~ r1_orders_2(X32,X34,X35)
        | X35 = k10_lattice3(X32,X33,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v1_lattice3(X32)
        | ~ l1_orders_2(X32) )
      & ( r1_orders_2(X32,X33,esk2_4(X32,X33,X34,X35))
        | ~ r1_orders_2(X32,X33,X35)
        | ~ r1_orders_2(X32,X34,X35)
        | X35 = k10_lattice3(X32,X33,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v1_lattice3(X32)
        | ~ l1_orders_2(X32) )
      & ( r1_orders_2(X32,X34,esk2_4(X32,X33,X34,X35))
        | ~ r1_orders_2(X32,X33,X35)
        | ~ r1_orders_2(X32,X34,X35)
        | X35 = k10_lattice3(X32,X33,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v1_lattice3(X32)
        | ~ l1_orders_2(X32) )
      & ( ~ r1_orders_2(X32,X35,esk2_4(X32,X33,X34,X35))
        | ~ r1_orders_2(X32,X33,X35)
        | ~ r1_orders_2(X32,X34,X35)
        | X35 = k10_lattice3(X32,X33,X34)
        | ~ m1_subset_1(X35,u1_struct_0(X32))
        | ~ m1_subset_1(X34,u1_struct_0(X32))
        | ~ m1_subset_1(X33,u1_struct_0(X32))
        | v2_struct_0(X32)
        | ~ v5_orders_2(X32)
        | ~ v1_lattice3(X32)
        | ~ l1_orders_2(X32) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).

fof(c_0_56,plain,(
    ! [X24] :
      ( ~ l1_orders_2(X24)
      | ~ v1_lattice3(X24)
      | ~ v2_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

cnf(c_0_57,negated_conjecture,
    ( k13_lattice3(esk4_0,X1,esk6_0) = k10_lattice3(esk4_0,X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43,c_0_38]),c_0_44]),c_0_45]),c_0_24])])).

cnf(c_0_58,plain,
    ( k12_lattice3(X1,X2,X3) = k11_lattice3(X1,X2,X3)
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_59,negated_conjecture,
    ( k12_lattice3(esk4_0,X1,esk5_0) = k12_lattice3(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47,c_0_42]),c_0_44]),c_0_48]),c_0_24])])).

cnf(c_0_60,negated_conjecture,
    ( m1_subset_1(k10_lattice3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_49,c_0_42])).

cnf(c_0_61,plain,
    ( X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,esk3_4(X1,X2,X3,X4),X4)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,plain,
    ( ~ l1_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_51])).

cnf(c_0_63,plain,
    ( r1_orders_2(X3,X1,X2)
    | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))
    | ~ m1_subset_1(X2,u1_struct_0(X3))
    | ~ m1_subset_1(X1,u1_struct_0(X3))
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_52])).

cnf(c_0_64,negated_conjecture,
    ( r2_hidden(k4_tarski(esk5_0,esk5_0),u1_orders_2(esk4_0))
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,plain,
    ( r1_orders_2(X1,X2,X3)
    | v2_struct_0(X1)
    | X3 != k10_lattice3(X1,X2,X4)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_55])).

cnf(c_0_66,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( k12_lattice3(esk4_0,esk5_0,k13_lattice3(esk4_0,esk5_0,esk6_0)) != esk5_0 ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_68,negated_conjecture,
    ( k13_lattice3(esk4_0,esk5_0,esk6_0) = k10_lattice3(esk4_0,esk5_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_57,c_0_42])).

cnf(c_0_69,negated_conjecture,
    ( k12_lattice3(esk4_0,X1,esk5_0) = k11_lattice3(esk4_0,X1,esk5_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_42]),c_0_44]),c_0_48]),c_0_24])])).

cnf(c_0_70,negated_conjecture,
    ( k12_lattice3(esk4_0,k10_lattice3(esk4_0,esk5_0,esk6_0),esk5_0) = k12_lattice3(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_59,c_0_60])).

cnf(c_0_71,plain,
    ( r1_orders_2(X1,esk3_4(X1,X2,X3,X4),X3)
    | X4 = k11_lattice3(X1,X2,X3)
    | v2_struct_0(X1)
    | ~ r1_orders_2(X1,X4,X2)
    | ~ r1_orders_2(X1,X4,X3)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ v2_lattice3(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_72,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ r1_orders_2(X2,esk3_4(X2,X3,X4,X1),X1)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[c_0_61,c_0_62])).

cnf(c_0_73,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,esk5_0)
    | v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_24]),c_0_42])])).

cnf(c_0_74,plain,
    ( r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_65,c_0_66])]),c_0_37])).

cnf(c_0_75,negated_conjecture,
    ( k12_lattice3(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_76,negated_conjecture,
    ( k12_lattice3(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0)) = k11_lattice3(esk4_0,k10_lattice3(esk4_0,esk5_0,esk6_0),esk5_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_60]),c_0_70])).

cnf(c_0_77,negated_conjecture,
    ( k12_lattice3(esk4_0,X1,k10_lattice3(esk4_0,esk5_0,esk6_0)) = k11_lattice3(esk4_0,X1,k10_lattice3(esk4_0,esk5_0,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_60]),c_0_44]),c_0_48]),c_0_24])])).

cnf(c_0_78,plain,
    ( X1 = k11_lattice3(X2,X3,X4)
    | r1_orders_2(X2,esk3_4(X2,X3,X4,X1),X4)
    | ~ v5_orders_2(X2)
    | ~ v2_lattice3(X2)
    | ~ r1_orders_2(X2,X1,X4)
    | ~ r1_orders_2(X2,X1,X3)
    | ~ l1_orders_2(X2)
    | ~ m1_subset_1(X1,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(csr,[status(thm)],[c_0_71,c_0_62])).

cnf(c_0_79,negated_conjecture,
    ( k11_lattice3(esk4_0,X1,esk5_0) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk4_0,esk3_4(esk4_0,X1,esk5_0,esk5_0),esk5_0)
    | ~ r1_orders_2(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72,c_0_73]),c_0_44]),c_0_48]),c_0_24]),c_0_42])])).

cnf(c_0_80,negated_conjecture,
    ( r1_orders_2(esk4_0,X1,k10_lattice3(esk4_0,X1,esk6_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74,c_0_38]),c_0_44]),c_0_45]),c_0_24])])).

cnf(c_0_81,negated_conjecture,
    ( k11_lattice3(esk4_0,k10_lattice3(esk4_0,esk5_0,esk6_0),esk5_0) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_75,c_0_76])).

cnf(c_0_82,negated_conjecture,
    ( k11_lattice3(esk4_0,k10_lattice3(esk4_0,esk5_0,esk6_0),esk5_0) = k11_lattice3(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77,c_0_42]),c_0_76])).

fof(c_0_83,plain,(
    ! [X17] :
      ( v2_struct_0(X17)
      | ~ l1_struct_0(X17)
      | ~ v1_xboole_0(u1_struct_0(X17)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_84,negated_conjecture,
    ( k11_lattice3(esk4_0,X1,esk5_0) = esk5_0
    | v1_xboole_0(u1_struct_0(esk4_0))
    | ~ r1_orders_2(esk4_0,esk5_0,X1)
    | ~ m1_subset_1(X1,u1_struct_0(esk4_0)) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_73]),c_0_44]),c_0_48]),c_0_24]),c_0_42])]),c_0_79])).

cnf(c_0_85,negated_conjecture,
    ( r1_orders_2(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0)) ),
    inference(spm,[status(thm)],[c_0_80,c_0_42])).

cnf(c_0_86,negated_conjecture,
    ( k11_lattice3(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0)) != esk5_0 ),
    inference(rw,[status(thm)],[c_0_81,c_0_82])).

cnf(c_0_87,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_83])).

cnf(c_0_88,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk4_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_85]),c_0_82]),c_0_60])]),c_0_86])).

cnf(c_0_89,negated_conjecture,
    ( ~ v2_struct_0(esk4_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_45]),c_0_24])])).

fof(c_0_90,plain,(
    ! [X22] :
      ( ~ l1_orders_2(X22)
      | l1_struct_0(X22) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

cnf(c_0_91,negated_conjecture,
    ( ~ l1_struct_0(esk4_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87,c_0_88]),c_0_89])).

cnf(c_0_92,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_90])).

cnf(c_0_93,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91,c_0_92]),c_0_24])]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.47/0.72  # AutoSched0-Mode selected heuristic G_E___208_B07_F1_SE_CS_SP_PS_S4d
% 0.47/0.72  # and selection function SelectCQIPrecWNTNp.
% 0.47/0.72  #
% 0.47/0.72  # Preprocessing time       : 0.030 s
% 0.47/0.72  # Presaturation interreduction done
% 0.47/0.72  
% 0.47/0.72  # Proof found!
% 0.47/0.72  # SZS status Theorem
% 0.47/0.72  # SZS output start CNFRefutation
% 0.47/0.72  fof(t18_lattice3, conjecture, ![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3))=X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_lattice3)).
% 0.47/0.72  fof(d4_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>(v3_orders_2(X1)<=>r1_relat_2(u1_orders_2(X1),u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_orders_2)).
% 0.47/0.72  fof(d1_relat_2, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(r1_relat_2(X1,X2)<=>![X3]:(r2_hidden(X3,X2)=>r2_hidden(k4_tarski(X3,X3),X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_2)).
% 0.47/0.72  fof(cc2_relat_1, axiom, ![X1]:(v1_relat_1(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>v1_relat_1(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 0.47/0.72  fof(dt_u1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_orders_2)).
% 0.47/0.72  fof(fc6_relat_1, axiom, ![X1, X2]:v1_relat_1(k2_zfmisc_1(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 0.47/0.72  fof(dt_k10_lattice3, axiom, ![X1, X2, X3]:(((l1_orders_2(X1)&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k10_lattice3)).
% 0.47/0.72  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.47/0.72  fof(redefinition_k13_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v1_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k13_lattice3)).
% 0.47/0.72  fof(commutativity_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k12_lattice3(X1,X3,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k12_lattice3)).
% 0.47/0.72  fof(redefinition_k12_lattice3, axiom, ![X1, X2, X3]:(((((v5_orders_2(X1)&v2_lattice3(X1))&l1_orders_2(X1))&m1_subset_1(X2,u1_struct_0(X1)))&m1_subset_1(X3,u1_struct_0(X1)))=>k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k12_lattice3)).
% 0.47/0.72  fof(l28_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k11_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X4,X2)&r1_orders_2(X1,X4,X3))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X5,X2)&r1_orders_2(X1,X5,X3))=>r1_orders_2(X1,X5,X4))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l28_lattice3)).
% 0.47/0.72  fof(cc2_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v2_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_lattice3)).
% 0.47/0.72  fof(d9_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(r1_orders_2(X1,X2,X3)<=>r2_hidden(k4_tarski(X2,X3),u1_orders_2(X1)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_orders_2)).
% 0.47/0.72  fof(l26_lattice3, axiom, ![X1]:((((~(v2_struct_0(X1))&v5_orders_2(X1))&v1_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>![X4]:(m1_subset_1(X4,u1_struct_0(X1))=>(X4=k10_lattice3(X1,X2,X3)<=>((r1_orders_2(X1,X2,X4)&r1_orders_2(X1,X3,X4))&![X5]:(m1_subset_1(X5,u1_struct_0(X1))=>((r1_orders_2(X1,X2,X5)&r1_orders_2(X1,X3,X5))=>r1_orders_2(X1,X4,X5))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l26_lattice3)).
% 0.47/0.72  fof(cc1_lattice3, axiom, ![X1]:(l1_orders_2(X1)=>(v1_lattice3(X1)=>~(v2_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_lattice3)).
% 0.47/0.72  fof(fc2_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>~(v1_xboole_0(u1_struct_0(X1)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 0.47/0.72  fof(dt_l1_orders_2, axiom, ![X1]:(l1_orders_2(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_orders_2)).
% 0.47/0.72  fof(c_0_18, negated_conjecture, ~(![X1]:(((((v3_orders_2(X1)&v5_orders_2(X1))&v1_lattice3(X1))&v2_lattice3(X1))&l1_orders_2(X1))=>![X2]:(m1_subset_1(X2,u1_struct_0(X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>k12_lattice3(X1,X2,k13_lattice3(X1,X2,X3))=X2)))), inference(assume_negation,[status(cth)],[t18_lattice3])).
% 0.47/0.72  fof(c_0_19, plain, ![X18]:((~v3_orders_2(X18)|r1_relat_2(u1_orders_2(X18),u1_struct_0(X18))|~l1_orders_2(X18))&(~r1_relat_2(u1_orders_2(X18),u1_struct_0(X18))|v3_orders_2(X18)|~l1_orders_2(X18))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_orders_2])])])).
% 0.47/0.72  fof(c_0_20, negated_conjecture, (((((v3_orders_2(esk4_0)&v5_orders_2(esk4_0))&v1_lattice3(esk4_0))&v2_lattice3(esk4_0))&l1_orders_2(esk4_0))&(m1_subset_1(esk5_0,u1_struct_0(esk4_0))&(m1_subset_1(esk6_0,u1_struct_0(esk4_0))&k12_lattice3(esk4_0,esk5_0,k13_lattice3(esk4_0,esk5_0,esk6_0))!=esk5_0))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_18])])])).
% 0.47/0.72  fof(c_0_21, plain, ![X12, X13, X14, X15]:((~r1_relat_2(X12,X13)|(~r2_hidden(X14,X13)|r2_hidden(k4_tarski(X14,X14),X12))|~v1_relat_1(X12))&((r2_hidden(esk1_2(X12,X15),X15)|r1_relat_2(X12,X15)|~v1_relat_1(X12))&(~r2_hidden(k4_tarski(esk1_2(X12,X15),esk1_2(X12,X15)),X12)|r1_relat_2(X12,X15)|~v1_relat_1(X12)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d1_relat_2])])])])])])).
% 0.47/0.72  cnf(c_0_22, plain, (r1_relat_2(u1_orders_2(X1),u1_struct_0(X1))|~v3_orders_2(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.47/0.72  cnf(c_0_23, negated_conjecture, (v3_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.72  cnf(c_0_24, negated_conjecture, (l1_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.72  fof(c_0_25, plain, ![X8, X9]:(~v1_relat_1(X8)|(~m1_subset_1(X9,k1_zfmisc_1(X8))|v1_relat_1(X9))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).
% 0.47/0.72  fof(c_0_26, plain, ![X23]:(~l1_orders_2(X23)|m1_subset_1(u1_orders_2(X23),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X23),u1_struct_0(X23))))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_u1_orders_2])])).
% 0.47/0.72  fof(c_0_27, plain, ![X10, X11]:v1_relat_1(k2_zfmisc_1(X10,X11)), inference(variable_rename,[status(thm)],[fc6_relat_1])).
% 0.47/0.72  fof(c_0_28, plain, ![X29, X30, X31]:(~l1_orders_2(X29)|~m1_subset_1(X30,u1_struct_0(X29))|~m1_subset_1(X31,u1_struct_0(X29))|m1_subset_1(k10_lattice3(X29,X30,X31),u1_struct_0(X29))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k10_lattice3])])).
% 0.47/0.72  cnf(c_0_29, plain, (r2_hidden(k4_tarski(X3,X3),X1)|~r1_relat_2(X1,X2)|~r2_hidden(X3,X2)|~v1_relat_1(X1)), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.47/0.72  cnf(c_0_30, negated_conjecture, (r1_relat_2(u1_orders_2(esk4_0),u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_22, c_0_23]), c_0_24])])).
% 0.47/0.72  cnf(c_0_31, plain, (v1_relat_1(X2)|~v1_relat_1(X1)|~m1_subset_1(X2,k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.47/0.72  cnf(c_0_32, plain, (m1_subset_1(u1_orders_2(X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X1))))|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_26])).
% 0.47/0.72  cnf(c_0_33, plain, (v1_relat_1(k2_zfmisc_1(X1,X2))), inference(split_conjunct,[status(thm)],[c_0_27])).
% 0.47/0.72  fof(c_0_34, plain, ![X6, X7]:(~m1_subset_1(X6,X7)|(v1_xboole_0(X7)|r2_hidden(X6,X7))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.47/0.72  fof(c_0_35, plain, ![X47, X48, X49]:(~v5_orders_2(X47)|~v1_lattice3(X47)|~l1_orders_2(X47)|~m1_subset_1(X48,u1_struct_0(X47))|~m1_subset_1(X49,u1_struct_0(X47))|k13_lattice3(X47,X48,X49)=k10_lattice3(X47,X48,X49)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k13_lattice3])])).
% 0.47/0.72  fof(c_0_36, plain, ![X26, X27, X28]:(~v5_orders_2(X26)|~v2_lattice3(X26)|~l1_orders_2(X26)|~m1_subset_1(X27,u1_struct_0(X26))|~m1_subset_1(X28,u1_struct_0(X26))|k12_lattice3(X26,X27,X28)=k12_lattice3(X26,X28,X27)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k12_lattice3])])).
% 0.47/0.72  cnf(c_0_37, plain, (m1_subset_1(k10_lattice3(X1,X2,X3),u1_struct_0(X1))|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_28])).
% 0.47/0.72  cnf(c_0_38, negated_conjecture, (m1_subset_1(esk6_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.72  cnf(c_0_39, negated_conjecture, (r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk4_0))|~v1_relat_1(u1_orders_2(esk4_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_29, c_0_30])).
% 0.47/0.72  cnf(c_0_40, plain, (v1_relat_1(u1_orders_2(X1))|~l1_orders_2(X1)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])])).
% 0.47/0.72  cnf(c_0_41, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.47/0.72  cnf(c_0_42, negated_conjecture, (m1_subset_1(esk5_0,u1_struct_0(esk4_0))), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.72  cnf(c_0_43, plain, (k13_lattice3(X1,X2,X3)=k10_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.47/0.72  cnf(c_0_44, negated_conjecture, (v5_orders_2(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.72  cnf(c_0_45, negated_conjecture, (v1_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.72  fof(c_0_46, plain, ![X44, X45, X46]:(~v5_orders_2(X44)|~v2_lattice3(X44)|~l1_orders_2(X44)|~m1_subset_1(X45,u1_struct_0(X44))|~m1_subset_1(X46,u1_struct_0(X44))|k12_lattice3(X44,X45,X46)=k11_lattice3(X44,X45,X46)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k12_lattice3])])).
% 0.47/0.72  cnf(c_0_47, plain, (k12_lattice3(X1,X2,X3)=k12_lattice3(X1,X3,X2)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.47/0.72  cnf(c_0_48, negated_conjecture, (v2_lattice3(esk4_0)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.72  cnf(c_0_49, negated_conjecture, (m1_subset_1(k10_lattice3(esk4_0,X1,esk6_0),u1_struct_0(esk4_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_37, c_0_38]), c_0_24])])).
% 0.47/0.72  fof(c_0_50, plain, ![X38, X39, X40, X41, X42]:((((r1_orders_2(X38,X41,X39)|X41!=k11_lattice3(X38,X39,X40)|~m1_subset_1(X41,u1_struct_0(X38))|~m1_subset_1(X40,u1_struct_0(X38))|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v5_orders_2(X38)|~v2_lattice3(X38)|~l1_orders_2(X38)))&(r1_orders_2(X38,X41,X40)|X41!=k11_lattice3(X38,X39,X40)|~m1_subset_1(X41,u1_struct_0(X38))|~m1_subset_1(X40,u1_struct_0(X38))|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v5_orders_2(X38)|~v2_lattice3(X38)|~l1_orders_2(X38))))&(~m1_subset_1(X42,u1_struct_0(X38))|(~r1_orders_2(X38,X42,X39)|~r1_orders_2(X38,X42,X40)|r1_orders_2(X38,X42,X41))|X41!=k11_lattice3(X38,X39,X40)|~m1_subset_1(X41,u1_struct_0(X38))|~m1_subset_1(X40,u1_struct_0(X38))|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v5_orders_2(X38)|~v2_lattice3(X38)|~l1_orders_2(X38))))&((m1_subset_1(esk3_4(X38,X39,X40,X41),u1_struct_0(X38))|(~r1_orders_2(X38,X41,X39)|~r1_orders_2(X38,X41,X40))|X41=k11_lattice3(X38,X39,X40)|~m1_subset_1(X41,u1_struct_0(X38))|~m1_subset_1(X40,u1_struct_0(X38))|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v5_orders_2(X38)|~v2_lattice3(X38)|~l1_orders_2(X38)))&(((r1_orders_2(X38,esk3_4(X38,X39,X40,X41),X39)|(~r1_orders_2(X38,X41,X39)|~r1_orders_2(X38,X41,X40))|X41=k11_lattice3(X38,X39,X40)|~m1_subset_1(X41,u1_struct_0(X38))|~m1_subset_1(X40,u1_struct_0(X38))|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v5_orders_2(X38)|~v2_lattice3(X38)|~l1_orders_2(X38)))&(r1_orders_2(X38,esk3_4(X38,X39,X40,X41),X40)|(~r1_orders_2(X38,X41,X39)|~r1_orders_2(X38,X41,X40))|X41=k11_lattice3(X38,X39,X40)|~m1_subset_1(X41,u1_struct_0(X38))|~m1_subset_1(X40,u1_struct_0(X38))|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v5_orders_2(X38)|~v2_lattice3(X38)|~l1_orders_2(X38))))&(~r1_orders_2(X38,esk3_4(X38,X39,X40,X41),X41)|(~r1_orders_2(X38,X41,X39)|~r1_orders_2(X38,X41,X40))|X41=k11_lattice3(X38,X39,X40)|~m1_subset_1(X41,u1_struct_0(X38))|~m1_subset_1(X40,u1_struct_0(X38))|~m1_subset_1(X39,u1_struct_0(X38))|(v2_struct_0(X38)|~v5_orders_2(X38)|~v2_lattice3(X38)|~l1_orders_2(X38)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l28_lattice3])])])])])])).
% 0.47/0.72  fof(c_0_51, plain, ![X25]:(~l1_orders_2(X25)|(~v2_lattice3(X25)|~v2_struct_0(X25))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc2_lattice3])])])).
% 0.47/0.72  fof(c_0_52, plain, ![X19, X20, X21]:((~r1_orders_2(X19,X20,X21)|r2_hidden(k4_tarski(X20,X21),u1_orders_2(X19))|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|~l1_orders_2(X19))&(~r2_hidden(k4_tarski(X20,X21),u1_orders_2(X19))|r1_orders_2(X19,X20,X21)|~m1_subset_1(X21,u1_struct_0(X19))|~m1_subset_1(X20,u1_struct_0(X19))|~l1_orders_2(X19))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_orders_2])])])])).
% 0.47/0.72  cnf(c_0_53, negated_conjecture, (r2_hidden(k4_tarski(X1,X1),u1_orders_2(esk4_0))|~r2_hidden(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39, c_0_40]), c_0_24])])).
% 0.47/0.72  cnf(c_0_54, negated_conjecture, (r2_hidden(esk5_0,u1_struct_0(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_41, c_0_42])).
% 0.47/0.72  fof(c_0_55, plain, ![X32, X33, X34, X35, X36]:((((r1_orders_2(X32,X33,X35)|X35!=k10_lattice3(X32,X33,X34)|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v5_orders_2(X32)|~v1_lattice3(X32)|~l1_orders_2(X32)))&(r1_orders_2(X32,X34,X35)|X35!=k10_lattice3(X32,X33,X34)|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v5_orders_2(X32)|~v1_lattice3(X32)|~l1_orders_2(X32))))&(~m1_subset_1(X36,u1_struct_0(X32))|(~r1_orders_2(X32,X33,X36)|~r1_orders_2(X32,X34,X36)|r1_orders_2(X32,X35,X36))|X35!=k10_lattice3(X32,X33,X34)|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v5_orders_2(X32)|~v1_lattice3(X32)|~l1_orders_2(X32))))&((m1_subset_1(esk2_4(X32,X33,X34,X35),u1_struct_0(X32))|(~r1_orders_2(X32,X33,X35)|~r1_orders_2(X32,X34,X35))|X35=k10_lattice3(X32,X33,X34)|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v5_orders_2(X32)|~v1_lattice3(X32)|~l1_orders_2(X32)))&(((r1_orders_2(X32,X33,esk2_4(X32,X33,X34,X35))|(~r1_orders_2(X32,X33,X35)|~r1_orders_2(X32,X34,X35))|X35=k10_lattice3(X32,X33,X34)|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v5_orders_2(X32)|~v1_lattice3(X32)|~l1_orders_2(X32)))&(r1_orders_2(X32,X34,esk2_4(X32,X33,X34,X35))|(~r1_orders_2(X32,X33,X35)|~r1_orders_2(X32,X34,X35))|X35=k10_lattice3(X32,X33,X34)|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v5_orders_2(X32)|~v1_lattice3(X32)|~l1_orders_2(X32))))&(~r1_orders_2(X32,X35,esk2_4(X32,X33,X34,X35))|(~r1_orders_2(X32,X33,X35)|~r1_orders_2(X32,X34,X35))|X35=k10_lattice3(X32,X33,X34)|~m1_subset_1(X35,u1_struct_0(X32))|~m1_subset_1(X34,u1_struct_0(X32))|~m1_subset_1(X33,u1_struct_0(X32))|(v2_struct_0(X32)|~v5_orders_2(X32)|~v1_lattice3(X32)|~l1_orders_2(X32)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[l26_lattice3])])])])])])).
% 0.47/0.72  fof(c_0_56, plain, ![X24]:(~l1_orders_2(X24)|(~v1_lattice3(X24)|~v2_struct_0(X24))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).
% 0.47/0.72  cnf(c_0_57, negated_conjecture, (k13_lattice3(esk4_0,X1,esk6_0)=k10_lattice3(esk4_0,X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_43, c_0_38]), c_0_44]), c_0_45]), c_0_24])])).
% 0.47/0.72  cnf(c_0_58, plain, (k12_lattice3(X1,X2,X3)=k11_lattice3(X1,X2,X3)|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X2,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.47/0.72  cnf(c_0_59, negated_conjecture, (k12_lattice3(esk4_0,X1,esk5_0)=k12_lattice3(esk4_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_47, c_0_42]), c_0_44]), c_0_48]), c_0_24])])).
% 0.47/0.72  cnf(c_0_60, negated_conjecture, (m1_subset_1(k10_lattice3(esk4_0,esk5_0,esk6_0),u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_49, c_0_42])).
% 0.47/0.72  cnf(c_0_61, plain, (X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,esk3_4(X1,X2,X3,X4),X4)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.47/0.72  cnf(c_0_62, plain, (~l1_orders_2(X1)|~v2_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_51])).
% 0.47/0.72  cnf(c_0_63, plain, (r1_orders_2(X3,X1,X2)|~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X3))|~m1_subset_1(X2,u1_struct_0(X3))|~m1_subset_1(X1,u1_struct_0(X3))|~l1_orders_2(X3)), inference(split_conjunct,[status(thm)],[c_0_52])).
% 0.47/0.72  cnf(c_0_64, negated_conjecture, (r2_hidden(k4_tarski(esk5_0,esk5_0),u1_orders_2(esk4_0))|v1_xboole_0(u1_struct_0(esk4_0))), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.47/0.72  cnf(c_0_65, plain, (r1_orders_2(X1,X2,X3)|v2_struct_0(X1)|X3!=k10_lattice3(X1,X2,X4)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_55])).
% 0.47/0.72  cnf(c_0_66, plain, (~l1_orders_2(X1)|~v1_lattice3(X1)|~v2_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_56])).
% 0.47/0.72  cnf(c_0_67, negated_conjecture, (k12_lattice3(esk4_0,esk5_0,k13_lattice3(esk4_0,esk5_0,esk6_0))!=esk5_0), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.47/0.72  cnf(c_0_68, negated_conjecture, (k13_lattice3(esk4_0,esk5_0,esk6_0)=k10_lattice3(esk4_0,esk5_0,esk6_0)), inference(spm,[status(thm)],[c_0_57, c_0_42])).
% 0.47/0.72  cnf(c_0_69, negated_conjecture, (k12_lattice3(esk4_0,X1,esk5_0)=k11_lattice3(esk4_0,X1,esk5_0)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_42]), c_0_44]), c_0_48]), c_0_24])])).
% 0.47/0.72  cnf(c_0_70, negated_conjecture, (k12_lattice3(esk4_0,k10_lattice3(esk4_0,esk5_0,esk6_0),esk5_0)=k12_lattice3(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_59, c_0_60])).
% 0.47/0.72  cnf(c_0_71, plain, (r1_orders_2(X1,esk3_4(X1,X2,X3,X4),X3)|X4=k11_lattice3(X1,X2,X3)|v2_struct_0(X1)|~r1_orders_2(X1,X4,X2)|~r1_orders_2(X1,X4,X3)|~m1_subset_1(X4,u1_struct_0(X1))|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))|~v5_orders_2(X1)|~v2_lattice3(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.47/0.72  cnf(c_0_72, plain, (X1=k11_lattice3(X2,X3,X4)|~v5_orders_2(X2)|~v2_lattice3(X2)|~r1_orders_2(X2,esk3_4(X2,X3,X4,X1),X1)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~l1_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[c_0_61, c_0_62])).
% 0.47/0.72  cnf(c_0_73, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,esk5_0)|v1_xboole_0(u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_24]), c_0_42])])).
% 0.47/0.72  cnf(c_0_74, plain, (r1_orders_2(X1,X2,k10_lattice3(X1,X2,X3))|~v5_orders_2(X1)|~v1_lattice3(X1)|~l1_orders_2(X1)|~m1_subset_1(X3,u1_struct_0(X1))|~m1_subset_1(X2,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[inference(csr,[status(thm)],[c_0_65, c_0_66])]), c_0_37])).
% 0.47/0.72  cnf(c_0_75, negated_conjecture, (k12_lattice3(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_67, c_0_68])).
% 0.47/0.72  cnf(c_0_76, negated_conjecture, (k12_lattice3(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0))=k11_lattice3(esk4_0,k10_lattice3(esk4_0,esk5_0,esk6_0),esk5_0)), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_60]), c_0_70])).
% 0.47/0.72  cnf(c_0_77, negated_conjecture, (k12_lattice3(esk4_0,X1,k10_lattice3(esk4_0,esk5_0,esk6_0))=k11_lattice3(esk4_0,X1,k10_lattice3(esk4_0,esk5_0,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58, c_0_60]), c_0_44]), c_0_48]), c_0_24])])).
% 0.47/0.72  cnf(c_0_78, plain, (X1=k11_lattice3(X2,X3,X4)|r1_orders_2(X2,esk3_4(X2,X3,X4,X1),X4)|~v5_orders_2(X2)|~v2_lattice3(X2)|~r1_orders_2(X2,X1,X4)|~r1_orders_2(X2,X1,X3)|~l1_orders_2(X2)|~m1_subset_1(X1,u1_struct_0(X2))|~m1_subset_1(X4,u1_struct_0(X2))|~m1_subset_1(X3,u1_struct_0(X2))), inference(csr,[status(thm)],[c_0_71, c_0_62])).
% 0.47/0.72  cnf(c_0_79, negated_conjecture, (k11_lattice3(esk4_0,X1,esk5_0)=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))|~r1_orders_2(esk4_0,esk3_4(esk4_0,X1,esk5_0,esk5_0),esk5_0)|~r1_orders_2(esk4_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_72, c_0_73]), c_0_44]), c_0_48]), c_0_24]), c_0_42])])).
% 0.47/0.72  cnf(c_0_80, negated_conjecture, (r1_orders_2(esk4_0,X1,k10_lattice3(esk4_0,X1,esk6_0))|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_74, c_0_38]), c_0_44]), c_0_45]), c_0_24])])).
% 0.47/0.72  cnf(c_0_81, negated_conjecture, (k11_lattice3(esk4_0,k10_lattice3(esk4_0,esk5_0,esk6_0),esk5_0)!=esk5_0), inference(rw,[status(thm)],[c_0_75, c_0_76])).
% 0.47/0.72  cnf(c_0_82, negated_conjecture, (k11_lattice3(esk4_0,k10_lattice3(esk4_0,esk5_0,esk6_0),esk5_0)=k11_lattice3(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0))), inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_77, c_0_42]), c_0_76])).
% 0.47/0.72  fof(c_0_83, plain, ![X17]:(v2_struct_0(X17)|~l1_struct_0(X17)|~v1_xboole_0(u1_struct_0(X17))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).
% 0.47/0.72  cnf(c_0_84, negated_conjecture, (k11_lattice3(esk4_0,X1,esk5_0)=esk5_0|v1_xboole_0(u1_struct_0(esk4_0))|~r1_orders_2(esk4_0,esk5_0,X1)|~m1_subset_1(X1,u1_struct_0(esk4_0))), inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78, c_0_73]), c_0_44]), c_0_48]), c_0_24]), c_0_42])]), c_0_79])).
% 0.47/0.72  cnf(c_0_85, negated_conjecture, (r1_orders_2(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0))), inference(spm,[status(thm)],[c_0_80, c_0_42])).
% 0.47/0.72  cnf(c_0_86, negated_conjecture, (k11_lattice3(esk4_0,esk5_0,k10_lattice3(esk4_0,esk5_0,esk6_0))!=esk5_0), inference(rw,[status(thm)],[c_0_81, c_0_82])).
% 0.47/0.72  cnf(c_0_87, plain, (v2_struct_0(X1)|~l1_struct_0(X1)|~v1_xboole_0(u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_83])).
% 0.47/0.72  cnf(c_0_88, negated_conjecture, (v1_xboole_0(u1_struct_0(esk4_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_84, c_0_85]), c_0_82]), c_0_60])]), c_0_86])).
% 0.47/0.72  cnf(c_0_89, negated_conjecture, (~v2_struct_0(esk4_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_45]), c_0_24])])).
% 0.47/0.72  fof(c_0_90, plain, ![X22]:(~l1_orders_2(X22)|l1_struct_0(X22)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).
% 0.47/0.72  cnf(c_0_91, negated_conjecture, (~l1_struct_0(esk4_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_87, c_0_88]), c_0_89])).
% 0.47/0.72  cnf(c_0_92, plain, (l1_struct_0(X1)|~l1_orders_2(X1)), inference(split_conjunct,[status(thm)],[c_0_90])).
% 0.47/0.72  cnf(c_0_93, negated_conjecture, ($false), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_91, c_0_92]), c_0_24])]), ['proof']).
% 0.47/0.72  # SZS output end CNFRefutation
% 0.47/0.72  # Proof object total steps             : 94
% 0.47/0.72  # Proof object clause steps            : 57
% 0.47/0.72  # Proof object formula steps           : 37
% 0.47/0.72  # Proof object conjectures             : 38
% 0.47/0.72  # Proof object clause conjectures      : 35
% 0.47/0.72  # Proof object formula conjectures     : 3
% 0.47/0.72  # Proof object initial clauses used    : 26
% 0.47/0.72  # Proof object initial formulas used   : 18
% 0.47/0.72  # Proof object generating inferences   : 25
% 0.47/0.72  # Proof object simplifying inferences  : 61
% 0.47/0.72  # Training examples: 0 positive, 0 negative
% 0.47/0.72  # Parsed axioms                        : 18
% 0.47/0.72  # Removed by relevancy pruning/SinE    : 0
% 0.47/0.72  # Initial clauses                      : 41
% 0.47/0.72  # Removed in clause preprocessing      : 0
% 0.47/0.72  # Initial clauses in saturation        : 41
% 0.47/0.72  # Processed clauses                    : 1179
% 0.47/0.72  # ...of these trivial                  : 10
% 0.47/0.72  # ...subsumed                          : 107
% 0.47/0.72  # ...remaining for further processing  : 1062
% 0.47/0.72  # Other redundant clauses eliminated   : 6
% 0.47/0.72  # Clauses deleted for lack of memory   : 0
% 0.47/0.72  # Backward-subsumed                    : 17
% 0.47/0.72  # Backward-rewritten                   : 122
% 0.47/0.72  # Generated clauses                    : 41372
% 0.47/0.72  # ...of the previous two non-trivial   : 41112
% 0.47/0.72  # Contextual simplify-reflections      : 23
% 0.47/0.72  # Paramodulations                      : 41366
% 0.47/0.72  # Factorizations                       : 0
% 0.47/0.72  # Equation resolutions                 : 6
% 0.47/0.72  # Propositional unsat checks           : 0
% 0.47/0.72  #    Propositional check models        : 0
% 0.47/0.72  #    Propositional check unsatisfiable : 0
% 0.47/0.72  #    Propositional clauses             : 0
% 0.47/0.72  #    Propositional clauses after purity: 0
% 0.47/0.72  #    Propositional unsat core size     : 0
% 0.47/0.72  #    Propositional preprocessing time  : 0.000
% 0.47/0.72  #    Propositional encoding time       : 0.000
% 0.47/0.72  #    Propositional solver time         : 0.000
% 0.47/0.72  #    Success case prop preproc time    : 0.000
% 0.47/0.72  #    Success case prop encoding time   : 0.000
% 0.47/0.72  #    Success case prop solver time     : 0.000
% 0.47/0.72  # Current number of processed clauses  : 876
% 0.47/0.72  #    Positive orientable unit clauses  : 430
% 0.47/0.72  #    Positive unorientable unit clauses: 0
% 0.47/0.72  #    Negative unit clauses             : 3
% 0.47/0.72  #    Non-unit-clauses                  : 443
% 0.47/0.72  # Current number of unprocessed clauses: 40014
% 0.47/0.72  # ...number of literals in the above   : 50752
% 0.47/0.72  # Current number of archived formulas  : 0
% 0.47/0.72  # Current number of archived clauses   : 180
% 0.47/0.72  # Clause-clause subsumption calls (NU) : 53791
% 0.47/0.72  # Rec. Clause-clause subsumption calls : 44680
% 0.47/0.72  # Non-unit clause-clause subsumptions  : 146
% 0.47/0.72  # Unit Clause-clause subsumption calls : 12343
% 0.47/0.72  # Rewrite failures with RHS unbound    : 0
% 0.47/0.72  # BW rewrite match attempts            : 7282
% 0.47/0.72  # BW rewrite match successes           : 21
% 0.47/0.72  # Condensation attempts                : 0
% 0.47/0.72  # Condensation successes               : 0
% 0.47/0.72  # Termbank termtop insertions          : 1452507
% 0.57/0.73  
% 0.57/0.73  # -------------------------------------------------
% 0.57/0.73  # User time                : 0.363 s
% 0.57/0.73  # System time              : 0.024 s
% 0.57/0.73  # Total time               : 0.387 s
% 0.57/0.73  # Maximum resident set size: 1592 pages
%------------------------------------------------------------------------------
