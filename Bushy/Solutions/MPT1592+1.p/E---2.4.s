%------------------------------------------------------------------------------
% File       : E---2.4
% Problem    : yellow_0__t71_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:48 EDT 2019

% Result     : Theorem 151.99s
% Output     : CNFRefutation 151.99s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 403 expanded)
%              Number of clauses        :   62 ( 144 expanded)
%              Number of leaves         :   18 ( 101 expanded)
%              Depth                    :    9
%              Number of atoms          :  543 (3578 expanded)
%              Number of equality atoms :   28 ( 552 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   40 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t41_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k13_lattice3(X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',t41_yellow_0)).

fof(redefinition_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',redefinition_k7_domain_1)).

fof(t71_yellow_0,conjecture,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & v6_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => ! [X4] :
                  ( m1_subset_1(X4,u1_struct_0(X2))
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X1))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X1))
                         => ( ( X5 = X3
                              & X6 = X4 )
                           => k13_lattice3(X2,X3,X4) = k13_lattice3(X1,X5,X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',t71_yellow_0)).

fof(t65_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v4_yellow_0(X2,X1)
            & m1_yellow_0(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
             => ( ( r1_yellow_0(X1,X3)
                  & r2_hidden(k1_yellow_0(X1,X3),u1_struct_0(X2)) )
               => ( r1_yellow_0(X2,X3)
                  & k1_yellow_0(X2,X3) = k1_yellow_0(X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',t65_yellow_0)).

fof(t20_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ( v1_lattice3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => r1_yellow_0(X1,k2_tarski(X2,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',t20_yellow_0)).

fof(cc1_lattice3,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ( v1_lattice3(X1)
       => ~ v2_struct_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',cc1_lattice3)).

fof(dt_k7_domain_1,axiom,(
    ! [X1,X2,X3] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1)
        & m1_subset_1(X3,X1) )
     => m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',dt_k7_domain_1)).

fof(d17_yellow_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v6_yellow_0(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X1))
                   => ( ( r2_hidden(X3,u1_struct_0(X2))
                        & r2_hidden(X4,u1_struct_0(X2))
                        & r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X3,X4)) )
                     => r2_hidden(k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X3,X4)),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',d17_yellow_0)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',fc2_struct_0)).

fof(dt_l1_orders_2,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',dt_l1_orders_2)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',t2_subset)).

fof(t7_boole,axiom,(
    ! [X1,X2] :
      ~ ( r2_hidden(X1,X2)
        & v1_xboole_0(X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',t7_boole)).

fof(dt_m1_yellow_0,axiom,(
    ! [X1] :
      ( l1_orders_2(X1)
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => l1_orders_2(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',dt_m1_yellow_0)).

fof(t1_subset,axiom,(
    ! [X1,X2] :
      ( r2_hidden(X1,X2)
     => m1_subset_1(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',t1_subset)).

fof(cc12_yellow_0,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & v5_orders_2(X1)
        & v1_lattice3(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & v6_yellow_0(X2,X1) )
           => ( ~ v2_struct_0(X2)
              & v1_lattice3(X2)
              & v4_yellow_0(X2,X1)
              & v6_yellow_0(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',cc12_yellow_0)).

fof(cc8_yellow_0,axiom,(
    ! [X1] :
      ( ( v5_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
           => ( v5_orders_2(X2)
              & v4_yellow_0(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',cc8_yellow_0)).

fof(cc7_yellow_0,axiom,(
    ! [X1] :
      ( ( v4_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
           => ( v4_orders_2(X2)
              & v4_yellow_0(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',cc7_yellow_0)).

fof(cc6_yellow_0,axiom,(
    ! [X1] :
      ( ( v3_orders_2(X1)
        & l1_orders_2(X1) )
     => ! [X2] :
          ( m1_yellow_0(X2,X1)
         => ( v4_yellow_0(X2,X1)
           => ( v3_orders_2(X2)
              & v4_yellow_0(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t71_yellow_0.p',cc6_yellow_0)).

fof(c_0_18,plain,(
    ! [X66,X67,X68] :
      ( ~ v3_orders_2(X66)
      | ~ v4_orders_2(X66)
      | ~ v5_orders_2(X66)
      | ~ v1_lattice3(X66)
      | ~ l1_orders_2(X66)
      | ~ m1_subset_1(X67,u1_struct_0(X66))
      | ~ m1_subset_1(X68,u1_struct_0(X66))
      | k1_yellow_0(X66,k7_domain_1(u1_struct_0(X66),X67,X68)) = k13_lattice3(X66,X67,X68) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t41_yellow_0])])])).

fof(c_0_19,plain,(
    ! [X52,X53,X54] :
      ( v1_xboole_0(X52)
      | ~ m1_subset_1(X53,X52)
      | ~ m1_subset_1(X54,X52)
      | k7_domain_1(X52,X53,X54) = k2_tarski(X53,X54) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k7_domain_1])])])).

fof(c_0_20,negated_conjecture,(
    ~ ! [X1] :
        ( ( v3_orders_2(X1)
          & v4_orders_2(X1)
          & v5_orders_2(X1)
          & v1_lattice3(X1)
          & l1_orders_2(X1) )
       => ! [X2] :
            ( ( ~ v2_struct_0(X2)
              & v4_yellow_0(X2,X1)
              & v6_yellow_0(X2,X1)
              & m1_yellow_0(X2,X1) )
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X2))
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X2))
                   => ! [X5] :
                        ( m1_subset_1(X5,u1_struct_0(X1))
                       => ! [X6] :
                            ( m1_subset_1(X6,u1_struct_0(X1))
                           => ( ( X5 = X3
                                & X6 = X4 )
                             => k13_lattice3(X2,X3,X4) = k13_lattice3(X1,X5,X6) ) ) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t71_yellow_0])).

fof(c_0_21,plain,(
    ! [X75,X76,X77] :
      ( ( r1_yellow_0(X76,X77)
        | ~ r1_yellow_0(X75,X77)
        | ~ r2_hidden(k1_yellow_0(X75,X77),u1_struct_0(X76))
        | ~ m1_subset_1(X77,k1_zfmisc_1(u1_struct_0(X76)))
        | v2_struct_0(X76)
        | ~ v4_yellow_0(X76,X75)
        | ~ m1_yellow_0(X76,X75)
        | v2_struct_0(X75)
        | ~ v4_orders_2(X75)
        | ~ l1_orders_2(X75) )
      & ( k1_yellow_0(X76,X77) = k1_yellow_0(X75,X77)
        | ~ r1_yellow_0(X75,X77)
        | ~ r2_hidden(k1_yellow_0(X75,X77),u1_struct_0(X76))
        | ~ m1_subset_1(X77,k1_zfmisc_1(u1_struct_0(X76)))
        | v2_struct_0(X76)
        | ~ v4_yellow_0(X76,X75)
        | ~ m1_yellow_0(X76,X75)
        | v2_struct_0(X75)
        | ~ v4_orders_2(X75)
        | ~ l1_orders_2(X75) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t65_yellow_0])])])])])).

cnf(c_0_22,plain,
    ( k1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3)) = k13_lattice3(X1,X2,X3)
    | ~ v3_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v5_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ l1_orders_2(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,plain,
    ( v1_xboole_0(X1)
    | k7_domain_1(X1,X2,X3) = k2_tarski(X2,X3)
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

fof(c_0_24,plain,(
    ! [X57,X58,X59] :
      ( ( ~ v1_lattice3(X57)
        | ~ m1_subset_1(X58,u1_struct_0(X57))
        | ~ m1_subset_1(X59,u1_struct_0(X57))
        | r1_yellow_0(X57,k2_tarski(X58,X59))
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) )
      & ( m1_subset_1(esk13_1(X57),u1_struct_0(X57))
        | v1_lattice3(X57)
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) )
      & ( m1_subset_1(esk14_1(X57),u1_struct_0(X57))
        | v1_lattice3(X57)
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) )
      & ( ~ r1_yellow_0(X57,k2_tarski(esk13_1(X57),esk14_1(X57)))
        | v1_lattice3(X57)
        | ~ v5_orders_2(X57)
        | ~ l1_orders_2(X57) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_yellow_0])])])])])).

fof(c_0_25,plain,(
    ! [X85] :
      ( ~ l1_orders_2(X85)
      | ~ v1_lattice3(X85)
      | ~ v2_struct_0(X85) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc1_lattice3])])])).

fof(c_0_26,plain,(
    ! [X37,X38,X39] :
      ( v1_xboole_0(X37)
      | ~ m1_subset_1(X38,X37)
      | ~ m1_subset_1(X39,X37)
      | m1_subset_1(k7_domain_1(X37,X38,X39),k1_zfmisc_1(X37)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_domain_1])])])).

fof(c_0_27,plain,(
    ! [X23,X24,X25,X26] :
      ( ( ~ v6_yellow_0(X24,X23)
        | ~ m1_subset_1(X25,u1_struct_0(X23))
        | ~ m1_subset_1(X26,u1_struct_0(X23))
        | ~ r2_hidden(X25,u1_struct_0(X24))
        | ~ r2_hidden(X26,u1_struct_0(X24))
        | ~ r1_yellow_0(X23,k7_domain_1(u1_struct_0(X23),X25,X26))
        | r2_hidden(k1_yellow_0(X23,k7_domain_1(u1_struct_0(X23),X25,X26)),u1_struct_0(X24))
        | ~ m1_yellow_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk7_2(X23,X24),u1_struct_0(X23))
        | v6_yellow_0(X24,X23)
        | ~ m1_yellow_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( m1_subset_1(esk8_2(X23,X24),u1_struct_0(X23))
        | v6_yellow_0(X24,X23)
        | ~ m1_yellow_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( r2_hidden(esk7_2(X23,X24),u1_struct_0(X24))
        | v6_yellow_0(X24,X23)
        | ~ m1_yellow_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( r2_hidden(esk8_2(X23,X24),u1_struct_0(X24))
        | v6_yellow_0(X24,X23)
        | ~ m1_yellow_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( r1_yellow_0(X23,k7_domain_1(u1_struct_0(X23),esk7_2(X23,X24),esk8_2(X23,X24)))
        | v6_yellow_0(X24,X23)
        | ~ m1_yellow_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) )
      & ( ~ r2_hidden(k1_yellow_0(X23,k7_domain_1(u1_struct_0(X23),esk7_2(X23,X24),esk8_2(X23,X24))),u1_struct_0(X24))
        | v6_yellow_0(X24,X23)
        | ~ m1_yellow_0(X24,X23)
        | v2_struct_0(X23)
        | ~ l1_orders_2(X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d17_yellow_0])])])])])])).

fof(c_0_28,plain,(
    ! [X92] :
      ( v2_struct_0(X92)
      | ~ l1_struct_0(X92)
      | ~ v1_xboole_0(u1_struct_0(X92)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

fof(c_0_29,plain,(
    ! [X40] :
      ( ~ l1_orders_2(X40)
      | l1_struct_0(X40) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_orders_2])])).

fof(c_0_30,plain,(
    ! [X62,X63] :
      ( ~ m1_subset_1(X62,X63)
      | v1_xboole_0(X63)
      | r2_hidden(X62,X63) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_31,negated_conjecture,
    ( v3_orders_2(esk1_0)
    & v4_orders_2(esk1_0)
    & v5_orders_2(esk1_0)
    & v1_lattice3(esk1_0)
    & l1_orders_2(esk1_0)
    & ~ v2_struct_0(esk2_0)
    & v4_yellow_0(esk2_0,esk1_0)
    & v6_yellow_0(esk2_0,esk1_0)
    & m1_yellow_0(esk2_0,esk1_0)
    & m1_subset_1(esk3_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk4_0,u1_struct_0(esk2_0))
    & m1_subset_1(esk5_0,u1_struct_0(esk1_0))
    & m1_subset_1(esk6_0,u1_struct_0(esk1_0))
    & esk5_0 = esk3_0
    & esk6_0 = esk4_0
    & k13_lattice3(esk2_0,esk3_0,esk4_0) != k13_lattice3(esk1_0,esk5_0,esk6_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_20])])])])).

cnf(c_0_32,plain,
    ( k1_yellow_0(X1,X2) = k1_yellow_0(X3,X2)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | ~ r1_yellow_0(X3,X2)
    | ~ r2_hidden(k1_yellow_0(X3,X2),u1_struct_0(X1))
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v4_yellow_0(X1,X3)
    | ~ m1_yellow_0(X1,X3)
    | ~ v4_orders_2(X3)
    | ~ l1_orders_2(X3) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_33,plain,
    ( k1_yellow_0(X1,k2_tarski(X2,X3)) = k13_lattice3(X1,X2,X3)
    | v1_xboole_0(u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_34,plain,
    ( r1_yellow_0(X1,k2_tarski(X2,X3))
    | ~ v1_lattice3(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v5_orders_2(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_35,plain,
    ( ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v2_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_36,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k7_domain_1(X1,X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X2,X1)
    | ~ m1_subset_1(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_26])).

fof(c_0_37,plain,(
    ! [X79,X80] :
      ( ~ r2_hidden(X79,X80)
      | ~ v1_xboole_0(X80) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t7_boole])])).

cnf(c_0_38,plain,
    ( r2_hidden(k1_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4)),u1_struct_0(X1))
    | v2_struct_0(X2)
    | ~ v6_yellow_0(X1,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X2))
    | ~ m1_subset_1(X4,u1_struct_0(X2))
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r2_hidden(X4,u1_struct_0(X1))
    | ~ r1_yellow_0(X2,k7_domain_1(u1_struct_0(X2),X3,X4))
    | ~ m1_yellow_0(X1,X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_27])).

cnf(c_0_39,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_28])).

cnf(c_0_40,plain,
    ( l1_struct_0(X1)
    | ~ l1_orders_2(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

cnf(c_0_41,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_43,negated_conjecture,
    ( v1_lattice3(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_44,negated_conjecture,
    ( l1_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk4_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_46,negated_conjecture,
    ( esk6_0 = esk4_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

fof(c_0_47,plain,(
    ! [X41,X42] :
      ( ~ l1_orders_2(X41)
      | ~ m1_yellow_0(X42,X41)
      | l1_orders_2(X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_yellow_0])])])).

cnf(c_0_48,plain,
    ( k1_yellow_0(X1,k2_tarski(X2,X3)) = k13_lattice3(X4,X2,X3)
    | v1_xboole_0(u1_struct_0(X4))
    | v2_struct_0(X1)
    | ~ r2_hidden(k13_lattice3(X4,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_yellow_0(X1,X4)
    | ~ v4_yellow_0(X1,X4)
    | ~ l1_orders_2(X4)
    | ~ v1_lattice3(X4)
    | ~ v5_orders_2(X4)
    | ~ v4_orders_2(X4)
    | ~ v3_orders_2(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_32,c_0_33]),c_0_34]),c_0_35])).

cnf(c_0_49,plain,
    ( v1_xboole_0(X1)
    | m1_subset_1(k2_tarski(X2,X3),k1_zfmisc_1(X1))
    | ~ m1_subset_1(X3,X1)
    | ~ m1_subset_1(X2,X1) ),
    inference(spm,[status(thm)],[c_0_36,c_0_23])).

cnf(c_0_50,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_51,plain,
    ( r2_hidden(k13_lattice3(X1,X2,X3),u1_struct_0(X4))
    | ~ r1_yellow_0(X1,k7_domain_1(u1_struct_0(X1),X2,X3))
    | ~ r2_hidden(X3,u1_struct_0(X4))
    | ~ r2_hidden(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_yellow_0(X4,X1)
    | ~ v6_yellow_0(X4,X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_22]),c_0_35])).

cnf(c_0_52,plain,
    ( r1_yellow_0(X1,k7_domain_1(X2,X3,X4))
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X4,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X4,X2)
    | ~ m1_subset_1(X3,X2)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_34,c_0_23])).

fof(c_0_53,plain,(
    ! [X55,X56] :
      ( ~ r2_hidden(X55,X56)
      | m1_subset_1(X55,X56) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_subset])])).

cnf(c_0_54,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1))
    | ~ l1_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_39,c_0_40])).

cnf(c_0_55,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk1_0))
    | r2_hidden(esk6_0,u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_42])).

cnf(c_0_56,negated_conjecture,
    ( ~ v2_struct_0(esk1_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_35,c_0_43]),c_0_44])])).

cnf(c_0_57,negated_conjecture,
    ( m1_subset_1(esk6_0,u1_struct_0(esk2_0)) ),
    inference(rw,[status(thm)],[c_0_45,c_0_46])).

cnf(c_0_58,plain,
    ( l1_orders_2(X2)
    | ~ l1_orders_2(X1)
    | ~ m1_yellow_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( m1_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_60,plain,
    ( k1_yellow_0(X1,k2_tarski(X2,X3)) = k13_lattice3(X4,X2,X3)
    | v1_xboole_0(u1_struct_0(X4))
    | v2_struct_0(X1)
    | ~ r2_hidden(k13_lattice3(X4,X2,X3),u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_yellow_0(X1,X4)
    | ~ v4_yellow_0(X1,X4)
    | ~ l1_orders_2(X4)
    | ~ v1_lattice3(X4)
    | ~ v5_orders_2(X4)
    | ~ v4_orders_2(X4)
    | ~ v3_orders_2(X4) ),
    inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_48,c_0_49]),c_0_50])).

cnf(c_0_61,plain,
    ( v1_xboole_0(u1_struct_0(X1))
    | r2_hidden(k13_lattice3(X1,X2,X3),u1_struct_0(X4))
    | ~ r2_hidden(X3,u1_struct_0(X4))
    | ~ r2_hidden(X2,u1_struct_0(X4))
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ m1_subset_1(X2,u1_struct_0(X1))
    | ~ m1_yellow_0(X4,X1)
    | ~ v6_yellow_0(X4,X1)
    | ~ l1_orders_2(X1)
    | ~ v1_lattice3(X1)
    | ~ v5_orders_2(X1)
    | ~ v4_orders_2(X1)
    | ~ v3_orders_2(X1) ),
    inference(spm,[status(thm)],[c_0_51,c_0_52])).

cnf(c_0_62,plain,
    ( m1_subset_1(X1,X2)
    | ~ r2_hidden(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_53])).

cnf(c_0_63,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_55]),c_0_44])]),c_0_56])).

fof(c_0_64,plain,(
    ! [X83,X84] :
      ( ( ~ v2_struct_0(X84)
        | v2_struct_0(X84)
        | ~ v4_yellow_0(X84,X83)
        | ~ v6_yellow_0(X84,X83)
        | ~ m1_yellow_0(X84,X83)
        | ~ v4_orders_2(X83)
        | ~ v5_orders_2(X83)
        | ~ v1_lattice3(X83)
        | ~ l1_orders_2(X83) )
      & ( v1_lattice3(X84)
        | v2_struct_0(X84)
        | ~ v4_yellow_0(X84,X83)
        | ~ v6_yellow_0(X84,X83)
        | ~ m1_yellow_0(X84,X83)
        | ~ v4_orders_2(X83)
        | ~ v5_orders_2(X83)
        | ~ v1_lattice3(X83)
        | ~ l1_orders_2(X83) )
      & ( v4_yellow_0(X84,X83)
        | v2_struct_0(X84)
        | ~ v4_yellow_0(X84,X83)
        | ~ v6_yellow_0(X84,X83)
        | ~ m1_yellow_0(X84,X83)
        | ~ v4_orders_2(X83)
        | ~ v5_orders_2(X83)
        | ~ v1_lattice3(X83)
        | ~ l1_orders_2(X83) )
      & ( v6_yellow_0(X84,X83)
        | v2_struct_0(X84)
        | ~ v4_yellow_0(X84,X83)
        | ~ v6_yellow_0(X84,X83)
        | ~ m1_yellow_0(X84,X83)
        | ~ v4_orders_2(X83)
        | ~ v5_orders_2(X83)
        | ~ v1_lattice3(X83)
        | ~ l1_orders_2(X83) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[cc12_yellow_0])])])])])).

fof(c_0_65,plain,(
    ! [X90,X91] :
      ( ( v5_orders_2(X91)
        | ~ v4_yellow_0(X91,X90)
        | ~ m1_yellow_0(X91,X90)
        | ~ v5_orders_2(X90)
        | ~ l1_orders_2(X90) )
      & ( v4_yellow_0(X91,X90)
        | ~ v4_yellow_0(X91,X90)
        | ~ m1_yellow_0(X91,X90)
        | ~ v5_orders_2(X90)
        | ~ l1_orders_2(X90) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc8_yellow_0])])])])).

fof(c_0_66,plain,(
    ! [X88,X89] :
      ( ( v4_orders_2(X89)
        | ~ v4_yellow_0(X89,X88)
        | ~ m1_yellow_0(X89,X88)
        | ~ v4_orders_2(X88)
        | ~ l1_orders_2(X88) )
      & ( v4_yellow_0(X89,X88)
        | ~ v4_yellow_0(X89,X88)
        | ~ m1_yellow_0(X89,X88)
        | ~ v4_orders_2(X88)
        | ~ l1_orders_2(X88) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc7_yellow_0])])])])).

fof(c_0_67,plain,(
    ! [X86,X87] :
      ( ( v3_orders_2(X87)
        | ~ v4_yellow_0(X87,X86)
        | ~ m1_yellow_0(X87,X86)
        | ~ v3_orders_2(X86)
        | ~ l1_orders_2(X86) )
      & ( v4_yellow_0(X87,X86)
        | ~ v4_yellow_0(X87,X86)
        | ~ m1_yellow_0(X87,X86)
        | ~ v3_orders_2(X86)
        | ~ l1_orders_2(X86) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc6_yellow_0])])])])).

cnf(c_0_68,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk6_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_57])).

cnf(c_0_69,negated_conjecture,
    ( l1_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_44])])).

cnf(c_0_70,negated_conjecture,
    ( ~ v2_struct_0(esk2_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_71,plain,
    ( k1_yellow_0(X1,k2_tarski(X2,X3)) = k13_lattice3(X4,X2,X3)
    | v1_xboole_0(u1_struct_0(X4))
    | v2_struct_0(X1)
    | ~ r2_hidden(X3,u1_struct_0(X1))
    | ~ r2_hidden(X2,u1_struct_0(X1))
    | ~ m1_subset_1(X3,u1_struct_0(X4))
    | ~ m1_subset_1(X2,u1_struct_0(X4))
    | ~ m1_yellow_0(X1,X4)
    | ~ v6_yellow_0(X1,X4)
    | ~ v4_yellow_0(X1,X4)
    | ~ l1_orders_2(X4)
    | ~ v1_lattice3(X4)
    | ~ v5_orders_2(X4)
    | ~ v4_orders_2(X4)
    | ~ v3_orders_2(X4) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(spm,[status(thm)],[c_0_60,c_0_61]),c_0_62]),c_0_62])).

cnf(c_0_72,negated_conjecture,
    ( v4_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_73,negated_conjecture,
    ( v6_yellow_0(esk2_0,esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_74,negated_conjecture,
    ( v5_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_75,negated_conjecture,
    ( v4_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_76,negated_conjecture,
    ( v3_orders_2(esk1_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_77,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk1_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_63])).

cnf(c_0_78,plain,
    ( v1_lattice3(X1)
    | v2_struct_0(X1)
    | ~ v4_yellow_0(X1,X2)
    | ~ v6_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ v4_orders_2(X2)
    | ~ v5_orders_2(X2)
    | ~ v1_lattice3(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_64])).

cnf(c_0_79,plain,
    ( v5_orders_2(X1)
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ v5_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_80,plain,
    ( v4_orders_2(X1)
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ v4_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_81,plain,
    ( v3_orders_2(X1)
    | ~ v4_yellow_0(X1,X2)
    | ~ m1_yellow_0(X1,X2)
    | ~ v3_orders_2(X2)
    | ~ l1_orders_2(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_67])).

cnf(c_0_82,negated_conjecture,
    ( r2_hidden(esk6_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_54,c_0_68]),c_0_69])]),c_0_70])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk2_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_84,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk4_0) != k13_lattice3(esk1_0,esk5_0,esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_85,negated_conjecture,
    ( esk5_0 = esk3_0 ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_86,negated_conjecture,
    ( k1_yellow_0(esk2_0,k2_tarski(X1,X2)) = k13_lattice3(esk1_0,X1,X2)
    | ~ r2_hidden(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_59]),c_0_73]),c_0_44]),c_0_43]),c_0_74]),c_0_75]),c_0_76])]),c_0_77]),c_0_70])).

cnf(c_0_87,negated_conjecture,
    ( v1_lattice3(esk2_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_72]),c_0_59]),c_0_73]),c_0_44]),c_0_43]),c_0_74]),c_0_75])]),c_0_70])).

cnf(c_0_88,negated_conjecture,
    ( v5_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_72]),c_0_59]),c_0_44]),c_0_74])])).

cnf(c_0_89,negated_conjecture,
    ( v4_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_80,c_0_72]),c_0_59]),c_0_44]),c_0_75])])).

cnf(c_0_90,negated_conjecture,
    ( v3_orders_2(esk2_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_72]),c_0_59]),c_0_44]),c_0_76])])).

cnf(c_0_91,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_50,c_0_82])).

cnf(c_0_92,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk2_0))
    | r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(spm,[status(thm)],[c_0_41,c_0_83])).

cnf(c_0_93,negated_conjecture,
    ( m1_subset_1(esk5_0,u1_struct_0(esk1_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_31])).

cnf(c_0_94,negated_conjecture,
    ( k13_lattice3(esk2_0,esk3_0,esk6_0) != k13_lattice3(esk1_0,esk3_0,esk6_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_46]),c_0_85])).

cnf(c_0_95,negated_conjecture,
    ( k13_lattice3(esk2_0,X1,X2) = k13_lattice3(esk1_0,X1,X2)
    | ~ r2_hidden(X2,u1_struct_0(esk2_0))
    | ~ r2_hidden(X1,u1_struct_0(esk2_0))
    | ~ m1_subset_1(X2,u1_struct_0(esk1_0))
    | ~ m1_subset_1(X1,u1_struct_0(esk1_0)) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_33,c_0_86]),c_0_69]),c_0_87]),c_0_88]),c_0_89]),c_0_90])]),c_0_91]),c_0_62]),c_0_62])).

cnf(c_0_96,negated_conjecture,
    ( r2_hidden(esk3_0,u1_struct_0(esk2_0)) ),
    inference(sr,[status(thm)],[c_0_92,c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( m1_subset_1(esk3_0,u1_struct_0(esk1_0)) ),
    inference(rw,[status(thm)],[c_0_93,c_0_85])).

cnf(c_0_98,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_94,c_0_95]),c_0_82]),c_0_96]),c_0_42]),c_0_97])]),
    [proof]).
%------------------------------------------------------------------------------
