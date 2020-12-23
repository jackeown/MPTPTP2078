%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 11:19:18 EST 2020

% Result     : Theorem 0.19s
% Output     : CNFRefutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 414 expanded)
%              Number of clauses        :   55 ( 157 expanded)
%              Number of leaves         :   16 ( 102 expanded)
%              Depth                    :   13
%              Number of atoms          :  309 (1817 expanded)
%              Number of equality atoms :   47 ( 266 expanded)
%              Maximal formula depth    :   21 (   4 average)
%              Maximal clause size      :   61 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t14_tex_2,conjecture,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ! [X3] :
              ( m1_pre_topc(X3,X1)
             => ( ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  & v1_tex_2(X2,X1) )
               => v1_tex_2(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_tex_2)).

fof(d3_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => ( v1_tex_2(X2,X1)
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
               => ( X3 = u1_struct_0(X2)
                 => v1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(t1_tsep_1,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(d7_subset_1,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X1))
     => ( v1_subset_1(X2,X1)
      <=> X2 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(dt_k1_pre_topc,axiom,(
    ! [X1,X2] :
      ( ( l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k1_pre_topc(X1,X2))
        & m1_pre_topc(k1_pre_topc(X1,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(dt_k2_subset_1,axiom,(
    ! [X1] : m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(d4_subset_1,axiom,(
    ! [X1] : k2_subset_1(X1) = X1 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(t65_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X1,X2)
          <=> m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(d10_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( v1_pre_topc(X3)
                & m1_pre_topc(X3,X1) )
             => ( X3 = k1_pre_topc(X1,X2)
              <=> k2_struct_0(X3) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(d9_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( l1_pre_topc(X2)
         => ( m1_pre_topc(X2,X1)
          <=> ( r1_tarski(k2_struct_0(X2),k2_struct_0(X1))
              & ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                 => ( r2_hidden(X3,u1_pre_topc(X2))
                  <=> ? [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                        & r2_hidden(X4,u1_pre_topc(X1))
                        & X3 = k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(t59_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
         => m1_pre_topc(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(d10_xboole_0,axiom,(
    ! [X1,X2] :
      ( X1 = X2
    <=> ( r1_tarski(X1,X2)
        & r1_tarski(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(fc14_subset_1,axiom,(
    ! [X1] : ~ v1_subset_1(k2_subset_1(X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

fof(c_0_16,negated_conjecture,(
    ~ ! [X1] :
        ( l1_pre_topc(X1)
       => ! [X2] :
            ( m1_pre_topc(X2,X1)
           => ! [X3] :
                ( m1_pre_topc(X3,X1)
               => ( ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                    & v1_tex_2(X2,X1) )
                 => v1_tex_2(X3,X1) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t14_tex_2])).

fof(c_0_17,plain,(
    ! [X33,X34,X35] :
      ( ( ~ v1_tex_2(X34,X33)
        | ~ m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))
        | X35 != u1_struct_0(X34)
        | v1_subset_1(X35,u1_struct_0(X33))
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( m1_subset_1(esk4_2(X33,X34),k1_zfmisc_1(u1_struct_0(X33)))
        | v1_tex_2(X34,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( esk4_2(X33,X34) = u1_struct_0(X34)
        | v1_tex_2(X34,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) )
      & ( ~ v1_subset_1(esk4_2(X33,X34),u1_struct_0(X33))
        | v1_tex_2(X34,X33)
        | ~ m1_pre_topc(X34,X33)
        | ~ l1_pre_topc(X33) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).

fof(c_0_18,negated_conjecture,
    ( l1_pre_topc(esk5_0)
    & m1_pre_topc(esk6_0,esk5_0)
    & m1_pre_topc(esk7_0,esk5_0)
    & g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))
    & v1_tex_2(esk6_0,esk5_0)
    & ~ v1_tex_2(esk7_0,esk5_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).

fof(c_0_19,plain,(
    ! [X31,X32] :
      ( ~ l1_pre_topc(X31)
      | ~ m1_pre_topc(X32,X31)
      | m1_subset_1(u1_struct_0(X32),k1_zfmisc_1(u1_struct_0(X31))) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).

cnf(c_0_20,plain,
    ( v1_tex_2(X2,X1)
    | ~ v1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_21,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_22,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_23,negated_conjecture,
    ( ~ v1_tex_2(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_24,plain,
    ( esk4_2(X1,X2) = u1_struct_0(X2)
    | v1_tex_2(X2,X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

fof(c_0_25,plain,(
    ! [X37,X38] :
      ( ( ~ v1_subset_1(X38,X37)
        | X38 != X37
        | ~ m1_subset_1(X38,k1_zfmisc_1(X37)) )
      & ( X38 = X37
        | v1_subset_1(X38,X37)
        | ~ m1_subset_1(X38,k1_zfmisc_1(X37)) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).

cnf(c_0_26,plain,
    ( m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,negated_conjecture,
    ( ~ v1_subset_1(esk4_2(esk5_0,esk7_0),u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22])]),c_0_23])).

cnf(c_0_28,negated_conjecture,
    ( esk4_2(esk5_0,esk7_0) = u1_struct_0(esk7_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_21]),c_0_22])]),c_0_23])).

fof(c_0_29,plain,(
    ! [X25,X26] :
      ( ~ l1_pre_topc(X25)
      | ~ m1_pre_topc(X26,X25)
      | l1_pre_topc(X26) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_30,plain,(
    ! [X22,X23] :
      ( ( v1_pre_topc(k1_pre_topc(X22,X23))
        | ~ l1_pre_topc(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))) )
      & ( m1_pre_topc(k1_pre_topc(X22,X23),X22)
        | ~ l1_pre_topc(X22)
        | ~ m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).

cnf(c_0_31,plain,
    ( X1 = X2
    | v1_subset_1(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_25])).

cnf(c_0_32,negated_conjecture,
    ( m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26,c_0_21]),c_0_22])])).

cnf(c_0_33,negated_conjecture,
    ( ~ v1_subset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0)) ),
    inference(rw,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_34,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_29])).

fof(c_0_35,plain,(
    ! [X8] : m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)) ),
    inference(variable_rename,[status(thm)],[dt_k2_subset_1])).

fof(c_0_36,plain,(
    ! [X7] : k2_subset_1(X7) = X7 ),
    inference(variable_rename,[status(thm)],[d4_subset_1])).

fof(c_0_37,plain,(
    ! [X24] :
      ( ~ l1_pre_topc(X24)
      | l1_struct_0(X24) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

cnf(c_0_38,negated_conjecture,
    ( m1_pre_topc(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

fof(c_0_39,plain,(
    ! [X29,X30] :
      ( ( ~ m1_pre_topc(X29,X30)
        | m1_pre_topc(X29,g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30)))
        | ~ l1_pre_topc(X30)
        | ~ l1_pre_topc(X29) )
      & ( ~ m1_pre_topc(X29,g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30)))
        | m1_pre_topc(X29,X30)
        | ~ l1_pre_topc(X30)
        | ~ l1_pre_topc(X29) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).

cnf(c_0_40,plain,
    ( m1_pre_topc(k1_pre_topc(X1,X2),X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_41,negated_conjecture,
    ( u1_struct_0(esk7_0) = u1_struct_0(esk5_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_32]),c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_21]),c_0_22])])).

cnf(c_0_43,plain,
    ( m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_35])).

cnf(c_0_44,plain,
    ( k2_subset_1(X1) = X1 ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

fof(c_0_45,plain,(
    ! [X10,X11,X12] :
      ( ( X12 != k1_pre_topc(X10,X11)
        | k2_struct_0(X12) = X11
        | ~ v1_pre_topc(X12)
        | ~ m1_pre_topc(X12,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) )
      & ( k2_struct_0(X12) != X11
        | X12 = k1_pre_topc(X10,X11)
        | ~ v1_pre_topc(X12)
        | ~ m1_pre_topc(X12,X10)
        | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))
        | ~ l1_pre_topc(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).

fof(c_0_46,plain,(
    ! [X14,X15,X16,X18,X20] :
      ( ( r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk1_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(X16,u1_pre_topc(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk1_3(X14,X15,X16),u1_pre_topc(X14))
        | ~ r2_hidden(X16,u1_pre_topc(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( X16 = k9_subset_1(u1_struct_0(X15),esk1_3(X14,X15,X16),k2_struct_0(X15))
        | ~ r2_hidden(X16,u1_pre_topc(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( ~ m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(X18,u1_pre_topc(X14))
        | X16 != k9_subset_1(u1_struct_0(X15),X18,k2_struct_0(X15))
        | r2_hidden(X16,u1_pre_topc(X15))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))
        | ~ m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk2_2(X14,X15),k1_zfmisc_1(u1_struct_0(X15)))
        | ~ r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( ~ r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X14)))
        | ~ r2_hidden(X20,u1_pre_topc(X14))
        | esk2_2(X14,X15) != k9_subset_1(u1_struct_0(X15),X20,k2_struct_0(X15))
        | ~ r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( m1_subset_1(esk3_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))
        | r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))
        | ~ r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( r2_hidden(esk3_2(X14,X15),u1_pre_topc(X14))
        | r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))
        | ~ r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) )
      & ( esk2_2(X14,X15) = k9_subset_1(u1_struct_0(X15),esk3_2(X14,X15),k2_struct_0(X15))
        | r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))
        | ~ r1_tarski(k2_struct_0(X15),k2_struct_0(X14))
        | m1_pre_topc(X15,X14)
        | ~ l1_pre_topc(X15)
        | ~ l1_pre_topc(X14) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).

fof(c_0_47,plain,(
    ! [X13] :
      ( ~ l1_struct_0(X13)
      | k2_struct_0(X13) = u1_struct_0(X13) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

cnf(c_0_48,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_49,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_38]),c_0_22])])).

fof(c_0_50,plain,(
    ! [X27,X28] :
      ( ~ l1_pre_topc(X27)
      | ~ m1_pre_topc(X28,g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))
      | m1_pre_topc(X28,X27) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).

cnf(c_0_51,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_52,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_53,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk7_0,X1),esk7_0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_42])])).

cnf(c_0_54,plain,
    ( m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(rw,[status(thm)],[c_0_43,c_0_44])).

cnf(c_0_55,plain,
    ( k2_struct_0(X1) = X3
    | X1 != k1_pre_topc(X2,X3)
    | ~ v1_pre_topc(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_45])).

cnf(c_0_56,plain,
    ( v1_pre_topc(k1_pre_topc(X1,X2))
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_30])).

cnf(c_0_57,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X1)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_46])).

cnf(c_0_58,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_59,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_49])).

cnf(c_0_60,negated_conjecture,
    ( l1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_22])).

cnf(c_0_61,plain,
    ( m1_pre_topc(X2,X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_62,negated_conjecture,
    ( g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0)) = g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk7_0)) ),
    inference(rw,[status(thm)],[c_0_51,c_0_41])).

cnf(c_0_63,plain,
    ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_52,c_0_34])).

cnf(c_0_64,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk7_0,u1_struct_0(esk5_0)),esk7_0) ),
    inference(spm,[status(thm)],[c_0_53,c_0_54])).

cnf(c_0_65,plain,
    ( k2_struct_0(k1_pre_topc(X1,X2)) = X2
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_55]),c_0_56]),c_0_40])).

fof(c_0_66,plain,(
    ! [X5,X6] :
      ( ( r1_tarski(X5,X6)
        | X5 != X6 )
      & ( r1_tarski(X6,X5)
        | X5 != X6 )
      & ( ~ r1_tarski(X5,X6)
        | ~ r1_tarski(X6,X5)
        | X5 = X6 ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).

cnf(c_0_67,plain,
    ( r1_tarski(k2_struct_0(X1),k2_struct_0(X2))
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[c_0_57,c_0_34])).

cnf(c_0_68,negated_conjecture,
    ( k2_struct_0(esk6_0) = u1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_59])).

cnf(c_0_69,negated_conjecture,
    ( k2_struct_0(esk5_0) = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_58,c_0_60])).

cnf(c_0_70,negated_conjecture,
    ( m1_pre_topc(X1,esk6_0)
    | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_62]),c_0_49])])).

cnf(c_0_71,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk7_0,u1_struct_0(esk5_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk7_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_64]),c_0_41]),c_0_42])])).

cnf(c_0_72,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk7_0,X1)) = X1
    | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_41]),c_0_42])])).

cnf(c_0_73,plain,
    ( v1_subset_1(X3,u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
    | X3 != u1_struct_0(X1)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_74,plain,
    ( X1 = X2
    | ~ r1_tarski(X1,X2)
    | ~ r1_tarski(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_66])).

cnf(c_0_75,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk6_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_38]),c_0_68]),c_0_69]),c_0_22])])).

cnf(c_0_76,negated_conjecture,
    ( m1_pre_topc(k1_pre_topc(esk7_0,u1_struct_0(esk5_0)),esk6_0) ),
    inference(spm,[status(thm)],[c_0_70,c_0_71])).

cnf(c_0_77,negated_conjecture,
    ( k2_struct_0(k1_pre_topc(esk7_0,u1_struct_0(esk5_0))) = u1_struct_0(esk5_0) ),
    inference(spm,[status(thm)],[c_0_72,c_0_54])).

fof(c_0_78,plain,(
    ! [X9] : ~ v1_subset_1(k2_subset_1(X9),X9) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).

cnf(c_0_79,plain,
    ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))
    | ~ v1_tex_2(X1,X2)
    | ~ m1_pre_topc(X1,X2)
    | ~ l1_pre_topc(X2) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_73]),c_0_26])).

cnf(c_0_80,negated_conjecture,
    ( v1_tex_2(esk6_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_81,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk5_0)
    | ~ r1_tarski(u1_struct_0(esk5_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_74,c_0_75])).

cnf(c_0_82,negated_conjecture,
    ( r1_tarski(u1_struct_0(esk5_0),u1_struct_0(esk6_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_76]),c_0_77]),c_0_68]),c_0_49])])).

cnf(c_0_83,plain,
    ( ~ v1_subset_1(k2_subset_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_78])).

cnf(c_0_84,negated_conjecture,
    ( v1_subset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79,c_0_80]),c_0_38]),c_0_22])])).

cnf(c_0_85,negated_conjecture,
    ( u1_struct_0(esk6_0) = u1_struct_0(esk5_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81,c_0_82])])).

cnf(c_0_86,plain,
    ( ~ v1_subset_1(X1,X1) ),
    inference(rw,[status(thm)],[c_0_83,c_0_44])).

cnf(c_0_87,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_84,c_0_85]),c_0_86]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:14:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  # Version: 2.5pre002
% 0.12/0.34  # No SInE strategy applied
% 0.12/0.34  # Trying AutoSched0 for 299 seconds
% 0.19/0.39  # AutoSched0-Mode selected heuristic G_E___208_C18_F1_SE_CS_SP_PS_S049N
% 0.19/0.39  # and selection function PSelectComplexPreferEQ.
% 0.19/0.39  #
% 0.19/0.39  # Preprocessing time       : 0.034 s
% 0.19/0.39  # Presaturation interreduction done
% 0.19/0.39  
% 0.19/0.39  # Proof found!
% 0.19/0.39  # SZS status Theorem
% 0.19/0.39  # SZS output start CNFRefutation
% 0.19/0.39  fof(t14_tex_2, conjecture, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>((g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))&v1_tex_2(X2,X1))=>v1_tex_2(X3,X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_tex_2)).
% 0.19/0.39  fof(d3_tex_2, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>(v1_tex_2(X2,X1)<=>![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))=>(X3=u1_struct_0(X2)=>v1_subset_1(X3,u1_struct_0(X1))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tex_2)).
% 0.19/0.39  fof(t1_tsep_1, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 0.19/0.39  fof(d7_subset_1, axiom, ![X1, X2]:(m1_subset_1(X2,k1_zfmisc_1(X1))=>(v1_subset_1(X2,X1)<=>X2!=X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_subset_1)).
% 0.19/0.39  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.19/0.39  fof(dt_k1_pre_topc, axiom, ![X1, X2]:((l1_pre_topc(X1)&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>(v1_pre_topc(k1_pre_topc(X1,X2))&m1_pre_topc(k1_pre_topc(X1,X2),X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_pre_topc)).
% 0.19/0.39  fof(dt_k2_subset_1, axiom, ![X1]:m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 0.19/0.39  fof(d4_subset_1, axiom, ![X1]:k2_subset_1(X1)=X1, file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 0.19/0.39  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.19/0.39  fof(t65_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X1,X2)<=>m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 0.19/0.39  fof(d10_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((v1_pre_topc(X3)&m1_pre_topc(X3,X1))=>(X3=k1_pre_topc(X1,X2)<=>k2_struct_0(X3)=X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_pre_topc)).
% 0.19/0.39  fof(d9_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(l1_pre_topc(X2)=>(m1_pre_topc(X2,X1)<=>(r1_tarski(k2_struct_0(X2),k2_struct_0(X1))&![X3]:(m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))=>(r2_hidden(X3,u1_pre_topc(X2))<=>?[X4]:((m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))&r2_hidden(X4,u1_pre_topc(X1)))&X3=k9_subset_1(u1_struct_0(X2),X4,k2_struct_0(X2))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_pre_topc)).
% 0.19/0.39  fof(d3_struct_0, axiom, ![X1]:(l1_struct_0(X1)=>k2_struct_0(X1)=u1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 0.19/0.39  fof(t59_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))=>m1_pre_topc(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 0.19/0.39  fof(d10_xboole_0, axiom, ![X1, X2]:(X1=X2<=>(r1_tarski(X1,X2)&r1_tarski(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 0.19/0.39  fof(fc14_subset_1, axiom, ![X1]:~(v1_subset_1(k2_subset_1(X1),X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 0.19/0.39  fof(c_0_16, negated_conjecture, ~(![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>![X3]:(m1_pre_topc(X3,X1)=>((g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))=g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))&v1_tex_2(X2,X1))=>v1_tex_2(X3,X1)))))), inference(assume_negation,[status(cth)],[t14_tex_2])).
% 0.19/0.39  fof(c_0_17, plain, ![X33, X34, X35]:((~v1_tex_2(X34,X33)|(~m1_subset_1(X35,k1_zfmisc_1(u1_struct_0(X33)))|(X35!=u1_struct_0(X34)|v1_subset_1(X35,u1_struct_0(X33))))|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))&((m1_subset_1(esk4_2(X33,X34),k1_zfmisc_1(u1_struct_0(X33)))|v1_tex_2(X34,X33)|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))&((esk4_2(X33,X34)=u1_struct_0(X34)|v1_tex_2(X34,X33)|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))&(~v1_subset_1(esk4_2(X33,X34),u1_struct_0(X33))|v1_tex_2(X34,X33)|~m1_pre_topc(X34,X33)|~l1_pre_topc(X33))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tex_2])])])])])).
% 0.19/0.39  fof(c_0_18, negated_conjecture, (l1_pre_topc(esk5_0)&(m1_pre_topc(esk6_0,esk5_0)&(m1_pre_topc(esk7_0,esk5_0)&((g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))&v1_tex_2(esk6_0,esk5_0))&~v1_tex_2(esk7_0,esk5_0))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_16])])])).
% 0.19/0.39  fof(c_0_19, plain, ![X31, X32]:(~l1_pre_topc(X31)|(~m1_pre_topc(X32,X31)|m1_subset_1(u1_struct_0(X32),k1_zfmisc_1(u1_struct_0(X31))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t1_tsep_1])])])).
% 0.19/0.39  cnf(c_0_20, plain, (v1_tex_2(X2,X1)|~v1_subset_1(esk4_2(X1,X2),u1_struct_0(X1))|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_21, negated_conjecture, (m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_22, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_23, negated_conjecture, (~v1_tex_2(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_24, plain, (esk4_2(X1,X2)=u1_struct_0(X2)|v1_tex_2(X2,X1)|~m1_pre_topc(X2,X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  fof(c_0_25, plain, ![X37, X38]:((~v1_subset_1(X38,X37)|X38!=X37|~m1_subset_1(X38,k1_zfmisc_1(X37)))&(X38=X37|v1_subset_1(X38,X37)|~m1_subset_1(X38,k1_zfmisc_1(X37)))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d7_subset_1])])])).
% 0.19/0.39  cnf(c_0_26, plain, (m1_subset_1(u1_struct_0(X2),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.19/0.39  cnf(c_0_27, negated_conjecture, (~v1_subset_1(esk4_2(esk5_0,esk7_0),u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20, c_0_21]), c_0_22])]), c_0_23])).
% 0.19/0.39  cnf(c_0_28, negated_conjecture, (esk4_2(esk5_0,esk7_0)=u1_struct_0(esk7_0)), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_21]), c_0_22])]), c_0_23])).
% 0.19/0.39  fof(c_0_29, plain, ![X25, X26]:(~l1_pre_topc(X25)|(~m1_pre_topc(X26,X25)|l1_pre_topc(X26))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.19/0.39  fof(c_0_30, plain, ![X22, X23]:((v1_pre_topc(k1_pre_topc(X22,X23))|(~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))))&(m1_pre_topc(k1_pre_topc(X22,X23),X22)|(~l1_pre_topc(X22)|~m1_subset_1(X23,k1_zfmisc_1(u1_struct_0(X22)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_k1_pre_topc])])])).
% 0.19/0.39  cnf(c_0_31, plain, (X1=X2|v1_subset_1(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_25])).
% 0.19/0.39  cnf(c_0_32, negated_conjecture, (m1_subset_1(u1_struct_0(esk7_0),k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_26, c_0_21]), c_0_22])])).
% 0.19/0.39  cnf(c_0_33, negated_conjecture, (~v1_subset_1(u1_struct_0(esk7_0),u1_struct_0(esk5_0))), inference(rw,[status(thm)],[c_0_27, c_0_28])).
% 0.19/0.39  cnf(c_0_34, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_29])).
% 0.19/0.39  fof(c_0_35, plain, ![X8]:m1_subset_1(k2_subset_1(X8),k1_zfmisc_1(X8)), inference(variable_rename,[status(thm)],[dt_k2_subset_1])).
% 0.19/0.39  fof(c_0_36, plain, ![X7]:k2_subset_1(X7)=X7, inference(variable_rename,[status(thm)],[d4_subset_1])).
% 0.19/0.39  fof(c_0_37, plain, ![X24]:(~l1_pre_topc(X24)|l1_struct_0(X24)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.19/0.39  cnf(c_0_38, negated_conjecture, (m1_pre_topc(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  fof(c_0_39, plain, ![X29, X30]:((~m1_pre_topc(X29,X30)|m1_pre_topc(X29,g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30)))|~l1_pre_topc(X30)|~l1_pre_topc(X29))&(~m1_pre_topc(X29,g1_pre_topc(u1_struct_0(X30),u1_pre_topc(X30)))|m1_pre_topc(X29,X30)|~l1_pre_topc(X30)|~l1_pre_topc(X29))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t65_pre_topc])])])])).
% 0.19/0.39  cnf(c_0_40, plain, (m1_pre_topc(k1_pre_topc(X1,X2),X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  cnf(c_0_41, negated_conjecture, (u1_struct_0(esk7_0)=u1_struct_0(esk5_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_31, c_0_32]), c_0_33])).
% 0.19/0.39  cnf(c_0_42, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_21]), c_0_22])])).
% 0.19/0.39  cnf(c_0_43, plain, (m1_subset_1(k2_subset_1(X1),k1_zfmisc_1(X1))), inference(split_conjunct,[status(thm)],[c_0_35])).
% 0.19/0.39  cnf(c_0_44, plain, (k2_subset_1(X1)=X1), inference(split_conjunct,[status(thm)],[c_0_36])).
% 0.19/0.39  fof(c_0_45, plain, ![X10, X11, X12]:((X12!=k1_pre_topc(X10,X11)|k2_struct_0(X12)=X11|(~v1_pre_topc(X12)|~m1_pre_topc(X12,X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))&(k2_struct_0(X12)!=X11|X12=k1_pre_topc(X10,X11)|(~v1_pre_topc(X12)|~m1_pre_topc(X12,X10))|~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X10)))|~l1_pre_topc(X10))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_pre_topc])])])])).
% 0.19/0.39  fof(c_0_46, plain, ![X14, X15, X16, X18, X20]:(((r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))&((((m1_subset_1(esk1_3(X14,X15,X16),k1_zfmisc_1(u1_struct_0(X14)))|~r2_hidden(X16,u1_pre_topc(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))&(r2_hidden(esk1_3(X14,X15,X16),u1_pre_topc(X14))|~r2_hidden(X16,u1_pre_topc(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14)))&(X16=k9_subset_1(u1_struct_0(X15),esk1_3(X14,X15,X16),k2_struct_0(X15))|~r2_hidden(X16,u1_pre_topc(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14)))&(~m1_subset_1(X18,k1_zfmisc_1(u1_struct_0(X14)))|~r2_hidden(X18,u1_pre_topc(X14))|X16!=k9_subset_1(u1_struct_0(X15),X18,k2_struct_0(X15))|r2_hidden(X16,u1_pre_topc(X15))|~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(X15)))|~m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))))&((m1_subset_1(esk2_2(X14,X15),k1_zfmisc_1(u1_struct_0(X15)))|~r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))&((~r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))|(~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(X14)))|~r2_hidden(X20,u1_pre_topc(X14))|esk2_2(X14,X15)!=k9_subset_1(u1_struct_0(X15),X20,k2_struct_0(X15)))|~r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))&(((m1_subset_1(esk3_2(X14,X15),k1_zfmisc_1(u1_struct_0(X14)))|r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))|~r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14))&(r2_hidden(esk3_2(X14,X15),u1_pre_topc(X14))|r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))|~r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14)))&(esk2_2(X14,X15)=k9_subset_1(u1_struct_0(X15),esk3_2(X14,X15),k2_struct_0(X15))|r2_hidden(esk2_2(X14,X15),u1_pre_topc(X15))|~r1_tarski(k2_struct_0(X15),k2_struct_0(X14))|m1_pre_topc(X15,X14)|~l1_pre_topc(X15)|~l1_pre_topc(X14)))))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d9_pre_topc])])])])])).
% 0.19/0.39  fof(c_0_47, plain, ![X13]:(~l1_struct_0(X13)|k2_struct_0(X13)=u1_struct_0(X13)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).
% 0.19/0.39  cnf(c_0_48, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_37])).
% 0.19/0.39  cnf(c_0_49, negated_conjecture, (l1_pre_topc(esk6_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34, c_0_38]), c_0_22])])).
% 0.19/0.39  fof(c_0_50, plain, ![X27, X28]:(~l1_pre_topc(X27)|(~m1_pre_topc(X28,g1_pre_topc(u1_struct_0(X27),u1_pre_topc(X27)))|m1_pre_topc(X28,X27))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t59_pre_topc])])])).
% 0.19/0.39  cnf(c_0_51, negated_conjecture, (g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=g1_pre_topc(u1_struct_0(esk7_0),u1_pre_topc(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_52, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.19/0.39  cnf(c_0_53, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk7_0,X1),esk7_0)|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_42])])).
% 0.19/0.39  cnf(c_0_54, plain, (m1_subset_1(X1,k1_zfmisc_1(X1))), inference(rw,[status(thm)],[c_0_43, c_0_44])).
% 0.19/0.39  cnf(c_0_55, plain, (k2_struct_0(X1)=X3|X1!=k1_pre_topc(X2,X3)|~v1_pre_topc(X1)|~m1_pre_topc(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_45])).
% 0.19/0.39  cnf(c_0_56, plain, (v1_pre_topc(k1_pre_topc(X1,X2))|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_30])).
% 0.19/0.39  cnf(c_0_57, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X1)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_46])).
% 0.19/0.39  cnf(c_0_58, plain, (k2_struct_0(X1)=u1_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.19/0.39  cnf(c_0_59, negated_conjecture, (l1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_48, c_0_49])).
% 0.19/0.39  cnf(c_0_60, negated_conjecture, (l1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_48, c_0_22])).
% 0.19/0.39  cnf(c_0_61, plain, (m1_pre_topc(X2,X1)|~l1_pre_topc(X1)|~m1_pre_topc(X2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.19/0.39  cnf(c_0_62, negated_conjecture, (g1_pre_topc(u1_struct_0(esk6_0),u1_pre_topc(esk6_0))=g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk7_0))), inference(rw,[status(thm)],[c_0_51, c_0_41])).
% 0.19/0.39  cnf(c_0_63, plain, (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_52, c_0_34])).
% 0.19/0.39  cnf(c_0_64, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk7_0,u1_struct_0(esk5_0)),esk7_0)), inference(spm,[status(thm)],[c_0_53, c_0_54])).
% 0.19/0.39  cnf(c_0_65, plain, (k2_struct_0(k1_pre_topc(X1,X2))=X2|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(csr,[status(thm)],[inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_55]), c_0_56]), c_0_40])).
% 0.19/0.39  fof(c_0_66, plain, ![X5, X6]:(((r1_tarski(X5,X6)|X5!=X6)&(r1_tarski(X6,X5)|X5!=X6))&(~r1_tarski(X5,X6)|~r1_tarski(X6,X5)|X5=X6)), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d10_xboole_0])])])).
% 0.19/0.39  cnf(c_0_67, plain, (r1_tarski(k2_struct_0(X1),k2_struct_0(X2))|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[c_0_57, c_0_34])).
% 0.19/0.39  cnf(c_0_68, negated_conjecture, (k2_struct_0(esk6_0)=u1_struct_0(esk6_0)), inference(spm,[status(thm)],[c_0_58, c_0_59])).
% 0.19/0.39  cnf(c_0_69, negated_conjecture, (k2_struct_0(esk5_0)=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_58, c_0_60])).
% 0.19/0.39  cnf(c_0_70, negated_conjecture, (m1_pre_topc(X1,esk6_0)|~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_62]), c_0_49])])).
% 0.19/0.39  cnf(c_0_71, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk7_0,u1_struct_0(esk5_0)),g1_pre_topc(u1_struct_0(esk5_0),u1_pre_topc(esk7_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_64]), c_0_41]), c_0_42])])).
% 0.19/0.39  cnf(c_0_72, negated_conjecture, (k2_struct_0(k1_pre_topc(esk7_0,X1))=X1|~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_41]), c_0_42])])).
% 0.19/0.39  cnf(c_0_73, plain, (v1_subset_1(X3,u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))|X3!=u1_struct_0(X1)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.19/0.39  cnf(c_0_74, plain, (X1=X2|~r1_tarski(X1,X2)|~r1_tarski(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_66])).
% 0.19/0.39  cnf(c_0_75, negated_conjecture, (r1_tarski(u1_struct_0(esk6_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_38]), c_0_68]), c_0_69]), c_0_22])])).
% 0.19/0.39  cnf(c_0_76, negated_conjecture, (m1_pre_topc(k1_pre_topc(esk7_0,u1_struct_0(esk5_0)),esk6_0)), inference(spm,[status(thm)],[c_0_70, c_0_71])).
% 0.19/0.39  cnf(c_0_77, negated_conjecture, (k2_struct_0(k1_pre_topc(esk7_0,u1_struct_0(esk5_0)))=u1_struct_0(esk5_0)), inference(spm,[status(thm)],[c_0_72, c_0_54])).
% 0.19/0.39  fof(c_0_78, plain, ![X9]:~v1_subset_1(k2_subset_1(X9),X9), inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc14_subset_1])])).
% 0.19/0.39  cnf(c_0_79, plain, (v1_subset_1(u1_struct_0(X1),u1_struct_0(X2))|~v1_tex_2(X1,X2)|~m1_pre_topc(X1,X2)|~l1_pre_topc(X2)), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_73]), c_0_26])).
% 0.19/0.39  cnf(c_0_80, negated_conjecture, (v1_tex_2(esk6_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.19/0.39  cnf(c_0_81, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk5_0)|~r1_tarski(u1_struct_0(esk5_0),u1_struct_0(esk6_0))), inference(spm,[status(thm)],[c_0_74, c_0_75])).
% 0.19/0.39  cnf(c_0_82, negated_conjecture, (r1_tarski(u1_struct_0(esk5_0),u1_struct_0(esk6_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67, c_0_76]), c_0_77]), c_0_68]), c_0_49])])).
% 0.19/0.39  cnf(c_0_83, plain, (~v1_subset_1(k2_subset_1(X1),X1)), inference(split_conjunct,[status(thm)],[c_0_78])).
% 0.19/0.39  cnf(c_0_84, negated_conjecture, (v1_subset_1(u1_struct_0(esk6_0),u1_struct_0(esk5_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_79, c_0_80]), c_0_38]), c_0_22])])).
% 0.19/0.39  cnf(c_0_85, negated_conjecture, (u1_struct_0(esk6_0)=u1_struct_0(esk5_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_81, c_0_82])])).
% 0.19/0.39  cnf(c_0_86, plain, (~v1_subset_1(X1,X1)), inference(rw,[status(thm)],[c_0_83, c_0_44])).
% 0.19/0.39  cnf(c_0_87, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(rw,[status(thm)],[c_0_84, c_0_85]), c_0_86]), ['proof']).
% 0.19/0.39  # SZS output end CNFRefutation
% 0.19/0.39  # Proof object total steps             : 88
% 0.19/0.39  # Proof object clause steps            : 55
% 0.19/0.39  # Proof object formula steps           : 33
% 0.19/0.39  # Proof object conjectures             : 34
% 0.19/0.39  # Proof object clause conjectures      : 31
% 0.19/0.39  # Proof object formula conjectures     : 3
% 0.19/0.39  # Proof object initial clauses used    : 24
% 0.19/0.39  # Proof object initial formulas used   : 16
% 0.19/0.39  # Proof object generating inferences   : 21
% 0.19/0.39  # Proof object simplifying inferences  : 48
% 0.19/0.39  # Training examples: 0 positive, 0 negative
% 0.19/0.39  # Parsed axioms                        : 16
% 0.19/0.39  # Removed by relevancy pruning/SinE    : 0
% 0.19/0.39  # Initial clauses                      : 39
% 0.19/0.39  # Removed in clause preprocessing      : 1
% 0.19/0.39  # Initial clauses in saturation        : 38
% 0.19/0.39  # Processed clauses                    : 137
% 0.19/0.39  # ...of these trivial                  : 0
% 0.19/0.39  # ...subsumed                          : 4
% 0.19/0.39  # ...remaining for further processing  : 133
% 0.19/0.39  # Other redundant clauses eliminated   : 7
% 0.19/0.39  # Clauses deleted for lack of memory   : 0
% 0.19/0.39  # Backward-subsumed                    : 2
% 0.19/0.39  # Backward-rewritten                   : 29
% 0.19/0.39  # Generated clauses                    : 241
% 0.19/0.39  # ...of the previous two non-trivial   : 198
% 0.19/0.39  # Contextual simplify-reflections      : 9
% 0.19/0.39  # Paramodulations                      : 234
% 0.19/0.39  # Factorizations                       : 0
% 0.19/0.39  # Equation resolutions                 : 7
% 0.19/0.39  # Propositional unsat checks           : 0
% 0.19/0.39  #    Propositional check models        : 0
% 0.19/0.39  #    Propositional check unsatisfiable : 0
% 0.19/0.39  #    Propositional clauses             : 0
% 0.19/0.39  #    Propositional clauses after purity: 0
% 0.19/0.39  #    Propositional unsat core size     : 0
% 0.19/0.39  #    Propositional preprocessing time  : 0.000
% 0.19/0.39  #    Propositional encoding time       : 0.000
% 0.19/0.39  #    Propositional solver time         : 0.000
% 0.19/0.39  #    Success case prop preproc time    : 0.000
% 0.19/0.39  #    Success case prop encoding time   : 0.000
% 0.19/0.39  #    Success case prop solver time     : 0.000
% 0.19/0.39  # Current number of processed clauses  : 60
% 0.19/0.39  #    Positive orientable unit clauses  : 32
% 0.19/0.39  #    Positive unorientable unit clauses: 0
% 0.19/0.39  #    Negative unit clauses             : 2
% 0.19/0.39  #    Non-unit-clauses                  : 26
% 0.19/0.39  # Current number of unprocessed clauses: 132
% 0.19/0.39  # ...number of literals in the above   : 348
% 0.19/0.39  # Current number of archived formulas  : 0
% 0.19/0.39  # Current number of archived clauses   : 67
% 0.19/0.39  # Clause-clause subsumption calls (NU) : 566
% 0.19/0.39  # Rec. Clause-clause subsumption calls : 83
% 0.19/0.39  # Non-unit clause-clause subsumptions  : 11
% 0.19/0.39  # Unit Clause-clause subsumption calls : 58
% 0.19/0.39  # Rewrite failures with RHS unbound    : 0
% 0.19/0.39  # BW rewrite match attempts            : 18
% 0.19/0.39  # BW rewrite match successes           : 6
% 0.19/0.39  # Condensation attempts                : 0
% 0.19/0.39  # Condensation successes               : 0
% 0.19/0.39  # Termbank termtop insertions          : 7968
% 0.19/0.39  
% 0.19/0.39  # -------------------------------------------------
% 0.19/0.39  # User time                : 0.046 s
% 0.19/0.39  # System time              : 0.007 s
% 0.19/0.39  # Total time               : 0.053 s
% 0.19/0.39  # Maximum resident set size: 1588 pages
%------------------------------------------------------------------------------
