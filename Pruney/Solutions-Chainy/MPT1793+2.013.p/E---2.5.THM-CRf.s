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
% DateTime   : Thu Dec  3 11:18:19 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 286 expanded)
%              Number of clauses        :   55 (  98 expanded)
%              Number of leaves         :   15 (  70 expanded)
%              Depth                    :   16
%              Number of atoms          :  370 (1794 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   23 (   5 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t109_tmap_1,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( ( ~ v2_struct_0(X3)
                & m1_pre_topc(X3,X1) )
             => ( r1_xboole_0(u1_struct_0(X3),X2)
               => ! [X4] :
                    ( m1_subset_1(X4,u1_struct_0(X3))
                   => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_tmap_1)).

fof(rc4_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ? [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
          & ~ v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc4_struct_0)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(dt_m1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_pre_topc(X2,X1)
         => l1_pre_topc(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(d3_tarski,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X1)
         => r2_hidden(X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(d1_xboole_0,axiom,(
    ! [X1] :
      ( v1_xboole_0(X1)
    <=> ! [X2] : ~ r2_hidden(X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(t55_pre_topc,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & m1_pre_topc(X2,X1) )
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X2))
             => m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_pre_topc)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(t64_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v2_struct_0(X2)
            & v2_pre_topc(X2)
            & l1_pre_topc(X2) )
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) )
             => ! [X4] :
                  ( ( ~ v2_struct_0(X4)
                    & m1_pre_topc(X4,X2) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X2))
                     => ! [X6] :
                          ( m1_subset_1(X6,u1_struct_0(X4))
                         => ( ( X5 = X6
                              & r1_tmap_1(X2,X1,X3,X5) )
                           => r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

fof(dt_k7_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_funct_1(k7_tmap_1(X1,X2))
        & v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
        & m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(dt_k6_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2))
        & l1_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(t108_tmap_1,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X1))
             => ( ~ r2_hidden(X3,X2)
               => r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_tmap_1)).

fof(fc4_tmap_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_struct_0(k6_tmap_1(X1,X2))
        & v1_pre_topc(k6_tmap_1(X1,X2))
        & v2_pre_topc(k6_tmap_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(c_0_15,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ! [X3] :
                ( ( ~ v2_struct_0(X3)
                  & m1_pre_topc(X3,X1) )
               => ( r1_xboole_0(u1_struct_0(X3),X2)
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X3))
                     => r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4) ) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t109_tmap_1])).

fof(c_0_16,plain,(
    ! [X34] :
      ( ( m1_subset_1(esk4_1(X34),k1_zfmisc_1(u1_struct_0(X34)))
        | v2_struct_0(X34)
        | ~ l1_struct_0(X34) )
      & ( ~ v1_xboole_0(esk4_1(X34))
        | v2_struct_0(X34)
        | ~ l1_struct_0(X34) ) ) ),
    inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc4_struct_0])])])])])).

fof(c_0_17,plain,(
    ! [X31] :
      ( ~ l1_pre_topc(X31)
      | l1_struct_0(X31) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_18,plain,(
    ! [X32,X33] :
      ( ~ l1_pre_topc(X32)
      | ~ m1_pre_topc(X33,X32)
      | l1_pre_topc(X33) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).

fof(c_0_19,negated_conjecture,
    ( ~ v2_struct_0(esk5_0)
    & v2_pre_topc(esk5_0)
    & l1_pre_topc(esk5_0)
    & m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))
    & ~ v2_struct_0(esk7_0)
    & m1_pre_topc(esk7_0,esk5_0)
    & r1_xboole_0(u1_struct_0(esk7_0),esk6_0)
    & m1_subset_1(esk8_0,u1_struct_0(esk7_0))
    & ~ r1_tmap_1(esk7_0,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk7_0),esk8_0) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).

fof(c_0_20,plain,(
    ! [X11,X12,X13,X14,X15] :
      ( ( ~ r1_tarski(X11,X12)
        | ~ r2_hidden(X13,X11)
        | r2_hidden(X13,X12) )
      & ( r2_hidden(esk2_2(X14,X15),X14)
        | r1_tarski(X14,X15) )
      & ( ~ r2_hidden(esk2_2(X14,X15),X15)
        | r1_tarski(X14,X15) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).

fof(c_0_21,plain,(
    ! [X29,X30] :
      ( ( ~ m1_subset_1(X29,k1_zfmisc_1(X30))
        | r1_tarski(X29,X30) )
      & ( ~ r1_tarski(X29,X30)
        | m1_subset_1(X29,k1_zfmisc_1(X30)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_22,plain,
    ( m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | v2_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_23,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_17])).

cnf(c_0_24,plain,
    ( l1_pre_topc(X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_18])).

cnf(c_0_25,negated_conjecture,
    ( m1_pre_topc(esk7_0,esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_26,negated_conjecture,
    ( l1_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_27,plain,
    ( r2_hidden(X3,X2)
    | ~ r1_tarski(X1,X2)
    | ~ r2_hidden(X3,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_28,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_29,plain,
    ( v2_struct_0(X1)
    | m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(spm,[status(thm)],[c_0_22,c_0_23])).

cnf(c_0_30,negated_conjecture,
    ( l1_pre_topc(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24,c_0_25]),c_0_26])])).

cnf(c_0_31,negated_conjecture,
    ( ~ v2_struct_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_32,plain,
    ( r2_hidden(X1,X2)
    | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
    | ~ r2_hidden(X1,X3) ),
    inference(spm,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_33,negated_conjecture,
    ( m1_subset_1(esk4_1(esk7_0),k1_zfmisc_1(u1_struct_0(esk7_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29,c_0_30]),c_0_31])).

fof(c_0_34,plain,(
    ! [X7,X8,X9] :
      ( ( ~ v1_xboole_0(X7)
        | ~ r2_hidden(X8,X7) )
      & ( r2_hidden(esk1_1(X9),X9)
        | v1_xboole_0(X9) ) ) ),
    inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).

cnf(c_0_35,negated_conjecture,
    ( r2_hidden(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk4_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_32,c_0_33])).

cnf(c_0_36,plain,
    ( r2_hidden(esk1_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_37,plain,
    ( ~ v1_xboole_0(X1)
    | ~ r2_hidden(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_34])).

cnf(c_0_38,negated_conjecture,
    ( r2_hidden(esk1_1(esk4_1(esk7_0)),u1_struct_0(esk7_0))
    | v1_xboole_0(esk4_1(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_35,c_0_36])).

fof(c_0_39,plain,(
    ! [X27,X28] :
      ( ~ m1_subset_1(X27,X28)
      | v1_xboole_0(X28)
      | r2_hidden(X27,X28) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

cnf(c_0_40,plain,
    ( v2_struct_0(X1)
    | ~ v1_xboole_0(esk4_1(X1))
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_41,negated_conjecture,
    ( v1_xboole_0(esk4_1(esk7_0))
    | ~ v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_37,c_0_38])).

fof(c_0_42,plain,(
    ! [X36,X37,X38] :
      ( v2_struct_0(X36)
      | ~ l1_pre_topc(X36)
      | v2_struct_0(X37)
      | ~ m1_pre_topc(X37,X36)
      | ~ m1_subset_1(X38,u1_struct_0(X37))
      | m1_subset_1(X38,u1_struct_0(X36)) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).

fof(c_0_43,plain,(
    ! [X19,X20,X22,X23,X24] :
      ( ( r2_hidden(esk3_2(X19,X20),X19)
        | r1_xboole_0(X19,X20) )
      & ( r2_hidden(esk3_2(X19,X20),X20)
        | r1_xboole_0(X19,X20) )
      & ( ~ r2_hidden(X24,X22)
        | ~ r2_hidden(X24,X23)
        | ~ r1_xboole_0(X22,X23) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_39])).

cnf(c_0_45,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk7_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_46,negated_conjecture,
    ( ~ l1_struct_0(esk7_0)
    | ~ v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40,c_0_41]),c_0_31])).

fof(c_0_47,plain,(
    ! [X48,X49,X50,X51,X52,X53] :
      ( v2_struct_0(X48)
      | ~ v2_pre_topc(X48)
      | ~ l1_pre_topc(X48)
      | v2_struct_0(X49)
      | ~ v2_pre_topc(X49)
      | ~ l1_pre_topc(X49)
      | ~ v1_funct_1(X50)
      | ~ v1_funct_2(X50,u1_struct_0(X49),u1_struct_0(X48))
      | ~ m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X48))))
      | v2_struct_0(X51)
      | ~ m1_pre_topc(X51,X49)
      | ~ m1_subset_1(X52,u1_struct_0(X49))
      | ~ m1_subset_1(X53,u1_struct_0(X51))
      | X52 != X53
      | ~ r1_tmap_1(X49,X48,X50,X52)
      | r1_tmap_1(X51,X48,k2_tmap_1(X49,X48,X50,X51),X53) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).

fof(c_0_48,plain,(
    ! [X41,X42] :
      ( ( v1_funct_1(k7_tmap_1(X41,X42))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))) )
      & ( v1_funct_2(k7_tmap_1(X41,X42),u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))) )
      & ( m1_subset_1(k7_tmap_1(X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))))
        | v2_struct_0(X41)
        | ~ v2_pre_topc(X41)
        | ~ l1_pre_topc(X41)
        | ~ m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).

fof(c_0_49,plain,(
    ! [X39,X40] :
      ( ( v1_pre_topc(k6_tmap_1(X39,X40))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))) )
      & ( v2_pre_topc(k6_tmap_1(X39,X40))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))) )
      & ( l1_pre_topc(k6_tmap_1(X39,X40))
        | v2_struct_0(X39)
        | ~ v2_pre_topc(X39)
        | ~ l1_pre_topc(X39)
        | ~ m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).

fof(c_0_50,plain,(
    ! [X45,X46,X47] :
      ( v2_struct_0(X45)
      | ~ v2_pre_topc(X45)
      | ~ l1_pre_topc(X45)
      | ~ m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))
      | ~ m1_subset_1(X47,u1_struct_0(X45))
      | r2_hidden(X47,X46)
      | r1_tmap_1(X45,k6_tmap_1(X45,X46),k7_tmap_1(X45,X46),X47) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t108_tmap_1])])])])).

cnf(c_0_51,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | m1_subset_1(X3,u1_struct_0(X1))
    | ~ l1_pre_topc(X1)
    | ~ m1_pre_topc(X2,X1)
    | ~ m1_subset_1(X3,u1_struct_0(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_42])).

cnf(c_0_52,plain,
    ( ~ r2_hidden(X1,X2)
    | ~ r2_hidden(X1,X3)
    | ~ r1_xboole_0(X2,X3) ),
    inference(split_conjunct,[status(thm)],[c_0_43])).

cnf(c_0_53,negated_conjecture,
    ( r1_xboole_0(u1_struct_0(esk7_0),esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_54,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk7_0))
    | v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_55,negated_conjecture,
    ( ~ v1_xboole_0(u1_struct_0(esk7_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46,c_0_23]),c_0_30])])).

cnf(c_0_56,plain,
    ( v2_struct_0(X1)
    | v2_struct_0(X2)
    | v2_struct_0(X4)
    | r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ v2_pre_topc(X2)
    | ~ l1_pre_topc(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
    | ~ m1_pre_topc(X4,X2)
    | ~ m1_subset_1(X5,u1_struct_0(X2))
    | ~ m1_subset_1(X6,u1_struct_0(X4))
    | X5 != X6
    | ~ r1_tmap_1(X2,X1,X3,X5) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

cnf(c_0_57,plain,
    ( m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_58,negated_conjecture,
    ( m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_59,negated_conjecture,
    ( v2_pre_topc(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_60,negated_conjecture,
    ( ~ v2_struct_0(esk5_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_61,plain,
    ( v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_62,plain,
    ( v1_funct_1(k7_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_48])).

cnf(c_0_63,plain,
    ( v2_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_64,plain,
    ( l1_pre_topc(k6_tmap_1(X1,X2))
    | v2_struct_0(X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_65,plain,
    ( v2_struct_0(X1)
    | r2_hidden(X3,X2)
    | r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ m1_subset_1(X3,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_50])).

cnf(c_0_66,negated_conjecture,
    ( v2_struct_0(X1)
    | m1_subset_1(esk8_0,u1_struct_0(X1))
    | ~ m1_pre_topc(esk7_0,X1)
    | ~ l1_pre_topc(X1) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51,c_0_45]),c_0_31])).

cnf(c_0_67,negated_conjecture,
    ( ~ r2_hidden(X1,u1_struct_0(esk7_0))
    | ~ r2_hidden(X1,esk6_0) ),
    inference(spm,[status(thm)],[c_0_52,c_0_53])).

cnf(c_0_68,negated_conjecture,
    ( r2_hidden(esk8_0,u1_struct_0(esk7_0)) ),
    inference(sr,[status(thm)],[c_0_54,c_0_55])).

cnf(c_0_69,plain,
    ( r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)
    | v2_struct_0(X1)
    | v2_struct_0(X3)
    | v2_struct_0(X2)
    | ~ r1_tmap_1(X3,X2,X4,X5)
    | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))
    | ~ v1_funct_1(X4)
    | ~ v2_pre_topc(X3)
    | ~ v2_pre_topc(X2)
    | ~ m1_pre_topc(X1,X3)
    | ~ l1_pre_topc(X3)
    | ~ l1_pre_topc(X2)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))
    | ~ m1_subset_1(X5,u1_struct_0(X1)) ),
    inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_56]),c_0_51])).

cnf(c_0_70,negated_conjecture,
    ( m1_subset_1(k7_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,esk6_0))))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_58]),c_0_59]),c_0_26])]),c_0_60])).

cnf(c_0_71,negated_conjecture,
    ( v1_funct_2(k7_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,esk6_0))) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61,c_0_58]),c_0_59]),c_0_26])]),c_0_60])).

cnf(c_0_72,negated_conjecture,
    ( v1_funct_1(k7_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62,c_0_58]),c_0_59]),c_0_26])]),c_0_60])).

cnf(c_0_73,negated_conjecture,
    ( v2_pre_topc(k6_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63,c_0_58]),c_0_59]),c_0_26])]),c_0_60])).

cnf(c_0_74,negated_conjecture,
    ( l1_pre_topc(k6_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64,c_0_58]),c_0_59]),c_0_26])]),c_0_60])).

cnf(c_0_75,negated_conjecture,
    ( r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1)
    | r2_hidden(X1,esk6_0)
    | ~ m1_subset_1(X1,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65,c_0_58]),c_0_59]),c_0_26])]),c_0_60])).

cnf(c_0_76,negated_conjecture,
    ( m1_subset_1(esk8_0,u1_struct_0(esk5_0)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_25]),c_0_26])]),c_0_60])).

cnf(c_0_77,negated_conjecture,
    ( ~ r2_hidden(esk8_0,esk6_0) ),
    inference(spm,[status(thm)],[c_0_67,c_0_68])).

cnf(c_0_78,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1),X2)
    | v2_struct_0(k6_tmap_1(esk5_0,esk6_0))
    | v2_struct_0(X1)
    | ~ r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X2)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69,c_0_70]),c_0_71]),c_0_72]),c_0_59]),c_0_73]),c_0_26]),c_0_74])]),c_0_60])).

cnf(c_0_79,negated_conjecture,
    ( r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk8_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75,c_0_76]),c_0_77])).

fof(c_0_80,plain,(
    ! [X43,X44] :
      ( ( ~ v2_struct_0(k6_tmap_1(X43,X44))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))) )
      & ( v1_pre_topc(k6_tmap_1(X43,X44))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))) )
      & ( v2_pre_topc(k6_tmap_1(X43,X44))
        | v2_struct_0(X43)
        | ~ v2_pre_topc(X43)
        | ~ l1_pre_topc(X43)
        | ~ m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).

cnf(c_0_81,negated_conjecture,
    ( r1_tmap_1(X1,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1),esk8_0)
    | v2_struct_0(k6_tmap_1(esk5_0,esk6_0))
    | v2_struct_0(X1)
    | ~ m1_pre_topc(X1,esk5_0)
    | ~ m1_subset_1(esk8_0,u1_struct_0(X1)) ),
    inference(spm,[status(thm)],[c_0_78,c_0_79])).

cnf(c_0_82,negated_conjecture,
    ( ~ r1_tmap_1(esk7_0,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk7_0),esk8_0) ),
    inference(split_conjunct,[status(thm)],[c_0_19])).

cnf(c_0_83,plain,
    ( v2_struct_0(X1)
    | ~ v2_struct_0(k6_tmap_1(X1,X2))
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(split_conjunct,[status(thm)],[c_0_80])).

cnf(c_0_84,negated_conjecture,
    ( v2_struct_0(k6_tmap_1(esk5_0,esk6_0)) ),
    inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_45]),c_0_25])]),c_0_82]),c_0_31])).

cnf(c_0_85,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83,c_0_84]),c_0_59]),c_0_26]),c_0_58])]),c_0_60]),
    [proof]).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:11:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  # Version: 2.5pre002
% 0.13/0.34  # No SInE strategy applied
% 0.13/0.34  # Trying AutoSched0 for 299 seconds
% 0.20/0.43  # AutoSched0-Mode selected heuristic G_E___302_C18_F1_URBAN_RG_S04BN
% 0.20/0.43  # and selection function PSelectComplexExceptUniqMaxHorn.
% 0.20/0.43  #
% 0.20/0.43  # Preprocessing time       : 0.040 s
% 0.20/0.43  
% 0.20/0.43  # Proof found!
% 0.20/0.43  # SZS status Theorem
% 0.20/0.43  # SZS output start CNFRefutation
% 0.20/0.43  fof(t109_tmap_1, conjecture, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_xboole_0(u1_struct_0(X3),X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_tmap_1)).
% 0.20/0.43  fof(rc4_struct_0, axiom, ![X1]:((~(v2_struct_0(X1))&l1_struct_0(X1))=>?[X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))&~(v1_xboole_0(X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc4_struct_0)).
% 0.20/0.43  fof(dt_l1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>l1_struct_0(X1)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 0.20/0.43  fof(dt_m1_pre_topc, axiom, ![X1]:(l1_pre_topc(X1)=>![X2]:(m1_pre_topc(X2,X1)=>l1_pre_topc(X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 0.20/0.43  fof(d3_tarski, axiom, ![X1, X2]:(r1_tarski(X1,X2)<=>![X3]:(r2_hidden(X3,X1)=>r2_hidden(X3,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 0.20/0.43  fof(t3_subset, axiom, ![X1, X2]:(m1_subset_1(X1,k1_zfmisc_1(X2))<=>r1_tarski(X1,X2)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 0.20/0.43  fof(d1_xboole_0, axiom, ![X1]:(v1_xboole_0(X1)<=>![X2]:~(r2_hidden(X2,X1))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 0.20/0.43  fof(t2_subset, axiom, ![X1, X2]:(m1_subset_1(X1,X2)=>(v1_xboole_0(X2)|r2_hidden(X1,X2))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 0.20/0.43  fof(t55_pre_topc, axiom, ![X1]:((~(v2_struct_0(X1))&l1_pre_topc(X1))=>![X2]:((~(v2_struct_0(X2))&m1_pre_topc(X2,X1))=>![X3]:(m1_subset_1(X3,u1_struct_0(X2))=>m1_subset_1(X3,u1_struct_0(X1))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_pre_topc)).
% 0.20/0.43  fof(t3_xboole_0, axiom, ![X1, X2]:(~((~(r1_xboole_0(X1,X2))&![X3]:~((r2_hidden(X3,X1)&r2_hidden(X3,X2)))))&~((?[X3]:(r2_hidden(X3,X1)&r2_hidden(X3,X2))&r1_xboole_0(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 0.20/0.43  fof(t64_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(((~(v2_struct_0(X2))&v2_pre_topc(X2))&l1_pre_topc(X2))=>![X3]:(((v1_funct_1(X3)&v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1)))&m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))))=>![X4]:((~(v2_struct_0(X4))&m1_pre_topc(X4,X2))=>![X5]:(m1_subset_1(X5,u1_struct_0(X2))=>![X6]:(m1_subset_1(X6,u1_struct_0(X4))=>((X5=X6&r1_tmap_1(X2,X1,X3,X5))=>r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 0.20/0.43  fof(dt_k7_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_funct_1(k7_tmap_1(X1,X2))&v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))&m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_tmap_1)).
% 0.20/0.43  fof(dt_k6_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((v1_pre_topc(k6_tmap_1(X1,X2))&v2_pre_topc(k6_tmap_1(X1,X2)))&l1_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_tmap_1)).
% 0.20/0.43  fof(t108_tmap_1, axiom, ![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:(m1_subset_1(X3,u1_struct_0(X1))=>(~(r2_hidden(X3,X2))=>r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_tmap_1)).
% 0.20/0.43  fof(fc4_tmap_1, axiom, ![X1, X2]:((((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))&m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))))=>((~(v2_struct_0(k6_tmap_1(X1,X2)))&v1_pre_topc(k6_tmap_1(X1,X2)))&v2_pre_topc(k6_tmap_1(X1,X2)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_tmap_1)).
% 0.20/0.43  fof(c_0_15, negated_conjecture, ~(![X1]:(((~(v2_struct_0(X1))&v2_pre_topc(X1))&l1_pre_topc(X1))=>![X2]:(m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))=>![X3]:((~(v2_struct_0(X3))&m1_pre_topc(X3,X1))=>(r1_xboole_0(u1_struct_0(X3),X2)=>![X4]:(m1_subset_1(X4,u1_struct_0(X3))=>r1_tmap_1(X3,k6_tmap_1(X1,X2),k2_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3),X4))))))), inference(assume_negation,[status(cth)],[t109_tmap_1])).
% 0.20/0.43  fof(c_0_16, plain, ![X34]:((m1_subset_1(esk4_1(X34),k1_zfmisc_1(u1_struct_0(X34)))|(v2_struct_0(X34)|~l1_struct_0(X34)))&(~v1_xboole_0(esk4_1(X34))|(v2_struct_0(X34)|~l1_struct_0(X34)))), inference(distribute,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[rc4_struct_0])])])])])).
% 0.20/0.43  fof(c_0_17, plain, ![X31]:(~l1_pre_topc(X31)|l1_struct_0(X31)), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).
% 0.20/0.43  fof(c_0_18, plain, ![X32, X33]:(~l1_pre_topc(X32)|(~m1_pre_topc(X33,X32)|l1_pre_topc(X33))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_m1_pre_topc])])])).
% 0.20/0.43  fof(c_0_19, negated_conjecture, (((~v2_struct_0(esk5_0)&v2_pre_topc(esk5_0))&l1_pre_topc(esk5_0))&(m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))&((~v2_struct_0(esk7_0)&m1_pre_topc(esk7_0,esk5_0))&(r1_xboole_0(u1_struct_0(esk7_0),esk6_0)&(m1_subset_1(esk8_0,u1_struct_0(esk7_0))&~r1_tmap_1(esk7_0,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk7_0),esk8_0)))))), inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_15])])])])).
% 0.20/0.43  fof(c_0_20, plain, ![X11, X12, X13, X14, X15]:((~r1_tarski(X11,X12)|(~r2_hidden(X13,X11)|r2_hidden(X13,X12)))&((r2_hidden(esk2_2(X14,X15),X14)|r1_tarski(X14,X15))&(~r2_hidden(esk2_2(X14,X15),X15)|r1_tarski(X14,X15)))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_tarski])])])])])])).
% 0.20/0.43  fof(c_0_21, plain, ![X29, X30]:((~m1_subset_1(X29,k1_zfmisc_1(X30))|r1_tarski(X29,X30))&(~r1_tarski(X29,X30)|m1_subset_1(X29,k1_zfmisc_1(X30)))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).
% 0.20/0.43  cnf(c_0_22, plain, (m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|v2_struct_0(X1)|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_23, plain, (l1_struct_0(X1)|~l1_pre_topc(X1)), inference(split_conjunct,[status(thm)],[c_0_17])).
% 0.20/0.43  cnf(c_0_24, plain, (l1_pre_topc(X2)|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_18])).
% 0.20/0.43  cnf(c_0_25, negated_conjecture, (m1_pre_topc(esk7_0,esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_26, negated_conjecture, (l1_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_27, plain, (r2_hidden(X3,X2)|~r1_tarski(X1,X2)|~r2_hidden(X3,X1)), inference(split_conjunct,[status(thm)],[c_0_20])).
% 0.20/0.43  cnf(c_0_28, plain, (r1_tarski(X1,X2)|~m1_subset_1(X1,k1_zfmisc_1(X2))), inference(split_conjunct,[status(thm)],[c_0_21])).
% 0.20/0.43  cnf(c_0_29, plain, (v2_struct_0(X1)|m1_subset_1(esk4_1(X1),k1_zfmisc_1(u1_struct_0(X1)))|~l1_pre_topc(X1)), inference(spm,[status(thm)],[c_0_22, c_0_23])).
% 0.20/0.43  cnf(c_0_30, negated_conjecture, (l1_pre_topc(esk7_0)), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_24, c_0_25]), c_0_26])])).
% 0.20/0.43  cnf(c_0_31, negated_conjecture, (~v2_struct_0(esk7_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_32, plain, (r2_hidden(X1,X2)|~m1_subset_1(X3,k1_zfmisc_1(X2))|~r2_hidden(X1,X3)), inference(spm,[status(thm)],[c_0_27, c_0_28])).
% 0.20/0.43  cnf(c_0_33, negated_conjecture, (m1_subset_1(esk4_1(esk7_0),k1_zfmisc_1(u1_struct_0(esk7_0)))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_29, c_0_30]), c_0_31])).
% 0.20/0.43  fof(c_0_34, plain, ![X7, X8, X9]:((~v1_xboole_0(X7)|~r2_hidden(X8,X7))&(r2_hidden(esk1_1(X9),X9)|v1_xboole_0(X9))), inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_xboole_0])])])])])])).
% 0.20/0.43  cnf(c_0_35, negated_conjecture, (r2_hidden(X1,u1_struct_0(esk7_0))|~r2_hidden(X1,esk4_1(esk7_0))), inference(spm,[status(thm)],[c_0_32, c_0_33])).
% 0.20/0.43  cnf(c_0_36, plain, (r2_hidden(esk1_1(X1),X1)|v1_xboole_0(X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.43  cnf(c_0_37, plain, (~v1_xboole_0(X1)|~r2_hidden(X2,X1)), inference(split_conjunct,[status(thm)],[c_0_34])).
% 0.20/0.43  cnf(c_0_38, negated_conjecture, (r2_hidden(esk1_1(esk4_1(esk7_0)),u1_struct_0(esk7_0))|v1_xboole_0(esk4_1(esk7_0))), inference(spm,[status(thm)],[c_0_35, c_0_36])).
% 0.20/0.43  fof(c_0_39, plain, ![X27, X28]:(~m1_subset_1(X27,X28)|(v1_xboole_0(X28)|r2_hidden(X27,X28))), inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).
% 0.20/0.43  cnf(c_0_40, plain, (v2_struct_0(X1)|~v1_xboole_0(esk4_1(X1))|~l1_struct_0(X1)), inference(split_conjunct,[status(thm)],[c_0_16])).
% 0.20/0.43  cnf(c_0_41, negated_conjecture, (v1_xboole_0(esk4_1(esk7_0))|~v1_xboole_0(u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_37, c_0_38])).
% 0.20/0.43  fof(c_0_42, plain, ![X36, X37, X38]:(v2_struct_0(X36)|~l1_pre_topc(X36)|(v2_struct_0(X37)|~m1_pre_topc(X37,X36)|(~m1_subset_1(X38,u1_struct_0(X37))|m1_subset_1(X38,u1_struct_0(X36))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t55_pre_topc])])])])).
% 0.20/0.43  fof(c_0_43, plain, ![X19, X20, X22, X23, X24]:(((r2_hidden(esk3_2(X19,X20),X19)|r1_xboole_0(X19,X20))&(r2_hidden(esk3_2(X19,X20),X20)|r1_xboole_0(X19,X20)))&(~r2_hidden(X24,X22)|~r2_hidden(X24,X23)|~r1_xboole_0(X22,X23))), inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t3_xboole_0])])])])])])])).
% 0.20/0.43  cnf(c_0_44, plain, (v1_xboole_0(X2)|r2_hidden(X1,X2)|~m1_subset_1(X1,X2)), inference(split_conjunct,[status(thm)],[c_0_39])).
% 0.20/0.43  cnf(c_0_45, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk7_0))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_46, negated_conjecture, (~l1_struct_0(esk7_0)|~v1_xboole_0(u1_struct_0(esk7_0))), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_40, c_0_41]), c_0_31])).
% 0.20/0.43  fof(c_0_47, plain, ![X48, X49, X50, X51, X52, X53]:(v2_struct_0(X48)|~v2_pre_topc(X48)|~l1_pre_topc(X48)|(v2_struct_0(X49)|~v2_pre_topc(X49)|~l1_pre_topc(X49)|(~v1_funct_1(X50)|~v1_funct_2(X50,u1_struct_0(X49),u1_struct_0(X48))|~m1_subset_1(X50,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X49),u1_struct_0(X48))))|(v2_struct_0(X51)|~m1_pre_topc(X51,X49)|(~m1_subset_1(X52,u1_struct_0(X49))|(~m1_subset_1(X53,u1_struct_0(X51))|(X52!=X53|~r1_tmap_1(X49,X48,X50,X52)|r1_tmap_1(X51,X48,k2_tmap_1(X49,X48,X50,X51),X53)))))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t64_tmap_1])])])])).
% 0.20/0.43  fof(c_0_48, plain, ![X41, X42]:(((v1_funct_1(k7_tmap_1(X41,X42))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))))&(v1_funct_2(k7_tmap_1(X41,X42),u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41))))))&(m1_subset_1(k7_tmap_1(X41,X42),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X41),u1_struct_0(k6_tmap_1(X41,X42)))))|(v2_struct_0(X41)|~v2_pre_topc(X41)|~l1_pre_topc(X41)|~m1_subset_1(X42,k1_zfmisc_1(u1_struct_0(X41)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k7_tmap_1])])])])).
% 0.20/0.43  fof(c_0_49, plain, ![X39, X40]:(((v1_pre_topc(k6_tmap_1(X39,X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))))&(v2_pre_topc(k6_tmap_1(X39,X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39))))))&(l1_pre_topc(k6_tmap_1(X39,X40))|(v2_struct_0(X39)|~v2_pre_topc(X39)|~l1_pre_topc(X39)|~m1_subset_1(X40,k1_zfmisc_1(u1_struct_0(X39)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[dt_k6_tmap_1])])])])).
% 0.20/0.43  fof(c_0_50, plain, ![X45, X46, X47]:(v2_struct_0(X45)|~v2_pre_topc(X45)|~l1_pre_topc(X45)|(~m1_subset_1(X46,k1_zfmisc_1(u1_struct_0(X45)))|(~m1_subset_1(X47,u1_struct_0(X45))|(r2_hidden(X47,X46)|r1_tmap_1(X45,k6_tmap_1(X45,X46),k7_tmap_1(X45,X46),X47))))), inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t108_tmap_1])])])])).
% 0.20/0.43  cnf(c_0_51, plain, (v2_struct_0(X1)|v2_struct_0(X2)|m1_subset_1(X3,u1_struct_0(X1))|~l1_pre_topc(X1)|~m1_pre_topc(X2,X1)|~m1_subset_1(X3,u1_struct_0(X2))), inference(split_conjunct,[status(thm)],[c_0_42])).
% 0.20/0.43  cnf(c_0_52, plain, (~r2_hidden(X1,X2)|~r2_hidden(X1,X3)|~r1_xboole_0(X2,X3)), inference(split_conjunct,[status(thm)],[c_0_43])).
% 0.20/0.43  cnf(c_0_53, negated_conjecture, (r1_xboole_0(u1_struct_0(esk7_0),esk6_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_54, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk7_0))|v1_xboole_0(u1_struct_0(esk7_0))), inference(spm,[status(thm)],[c_0_44, c_0_45])).
% 0.20/0.43  cnf(c_0_55, negated_conjecture, (~v1_xboole_0(u1_struct_0(esk7_0))), inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_46, c_0_23]), c_0_30])])).
% 0.20/0.43  cnf(c_0_56, plain, (v2_struct_0(X1)|v2_struct_0(X2)|v2_struct_0(X4)|r1_tmap_1(X4,X1,k2_tmap_1(X2,X1,X3,X4),X6)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~v2_pre_topc(X2)|~l1_pre_topc(X2)|~v1_funct_1(X3)|~v1_funct_2(X3,u1_struct_0(X2),u1_struct_0(X1))|~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))|~m1_pre_topc(X4,X2)|~m1_subset_1(X5,u1_struct_0(X2))|~m1_subset_1(X6,u1_struct_0(X4))|X5!=X6|~r1_tmap_1(X2,X1,X3,X5)), inference(split_conjunct,[status(thm)],[c_0_47])).
% 0.20/0.43  cnf(c_0_57, plain, (m1_subset_1(k7_tmap_1(X1,X2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.43  cnf(c_0_58, negated_conjecture, (m1_subset_1(esk6_0,k1_zfmisc_1(u1_struct_0(esk5_0)))), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_59, negated_conjecture, (v2_pre_topc(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_60, negated_conjecture, (~v2_struct_0(esk5_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_61, plain, (v1_funct_2(k7_tmap_1(X1,X2),u1_struct_0(X1),u1_struct_0(k6_tmap_1(X1,X2)))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.43  cnf(c_0_62, plain, (v1_funct_1(k7_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_48])).
% 0.20/0.43  cnf(c_0_63, plain, (v2_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.43  cnf(c_0_64, plain, (l1_pre_topc(k6_tmap_1(X1,X2))|v2_struct_0(X1)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_49])).
% 0.20/0.43  cnf(c_0_65, plain, (v2_struct_0(X1)|r2_hidden(X3,X2)|r1_tmap_1(X1,k6_tmap_1(X1,X2),k7_tmap_1(X1,X2),X3)|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))|~m1_subset_1(X3,u1_struct_0(X1))), inference(split_conjunct,[status(thm)],[c_0_50])).
% 0.20/0.43  cnf(c_0_66, negated_conjecture, (v2_struct_0(X1)|m1_subset_1(esk8_0,u1_struct_0(X1))|~m1_pre_topc(esk7_0,X1)|~l1_pre_topc(X1)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_51, c_0_45]), c_0_31])).
% 0.20/0.43  cnf(c_0_67, negated_conjecture, (~r2_hidden(X1,u1_struct_0(esk7_0))|~r2_hidden(X1,esk6_0)), inference(spm,[status(thm)],[c_0_52, c_0_53])).
% 0.20/0.43  cnf(c_0_68, negated_conjecture, (r2_hidden(esk8_0,u1_struct_0(esk7_0))), inference(sr,[status(thm)],[c_0_54, c_0_55])).
% 0.20/0.43  cnf(c_0_69, plain, (r1_tmap_1(X1,X2,k2_tmap_1(X3,X2,X4,X1),X5)|v2_struct_0(X1)|v2_struct_0(X3)|v2_struct_0(X2)|~r1_tmap_1(X3,X2,X4,X5)|~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X2))|~v1_funct_1(X4)|~v2_pre_topc(X3)|~v2_pre_topc(X2)|~m1_pre_topc(X1,X3)|~l1_pre_topc(X3)|~l1_pre_topc(X2)|~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X2))))|~m1_subset_1(X5,u1_struct_0(X1))), inference(csr,[status(thm)],[inference(er,[status(thm)],[c_0_56]), c_0_51])).
% 0.20/0.43  cnf(c_0_70, negated_conjecture, (m1_subset_1(k7_tmap_1(esk5_0,esk6_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,esk6_0)))))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_57, c_0_58]), c_0_59]), c_0_26])]), c_0_60])).
% 0.20/0.43  cnf(c_0_71, negated_conjecture, (v1_funct_2(k7_tmap_1(esk5_0,esk6_0),u1_struct_0(esk5_0),u1_struct_0(k6_tmap_1(esk5_0,esk6_0)))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_61, c_0_58]), c_0_59]), c_0_26])]), c_0_60])).
% 0.20/0.43  cnf(c_0_72, negated_conjecture, (v1_funct_1(k7_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_62, c_0_58]), c_0_59]), c_0_26])]), c_0_60])).
% 0.20/0.43  cnf(c_0_73, negated_conjecture, (v2_pre_topc(k6_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_63, c_0_58]), c_0_59]), c_0_26])]), c_0_60])).
% 0.20/0.43  cnf(c_0_74, negated_conjecture, (l1_pre_topc(k6_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_64, c_0_58]), c_0_59]), c_0_26])]), c_0_60])).
% 0.20/0.43  cnf(c_0_75, negated_conjecture, (r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1)|r2_hidden(X1,esk6_0)|~m1_subset_1(X1,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_65, c_0_58]), c_0_59]), c_0_26])]), c_0_60])).
% 0.20/0.43  cnf(c_0_76, negated_conjecture, (m1_subset_1(esk8_0,u1_struct_0(esk5_0))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66, c_0_25]), c_0_26])]), c_0_60])).
% 0.20/0.43  cnf(c_0_77, negated_conjecture, (~r2_hidden(esk8_0,esk6_0)), inference(spm,[status(thm)],[c_0_67, c_0_68])).
% 0.20/0.43  cnf(c_0_78, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1),X2)|v2_struct_0(k6_tmap_1(esk5_0,esk6_0))|v2_struct_0(X1)|~r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X2)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(X2,u1_struct_0(X1))), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_69, c_0_70]), c_0_71]), c_0_72]), c_0_59]), c_0_73]), c_0_26]), c_0_74])]), c_0_60])).
% 0.20/0.43  cnf(c_0_79, negated_conjecture, (r1_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk8_0)), inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_75, c_0_76]), c_0_77])).
% 0.20/0.43  fof(c_0_80, plain, ![X43, X44]:(((~v2_struct_0(k6_tmap_1(X43,X44))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))))&(v1_pre_topc(k6_tmap_1(X43,X44))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43))))))&(v2_pre_topc(k6_tmap_1(X43,X44))|(v2_struct_0(X43)|~v2_pre_topc(X43)|~l1_pre_topc(X43)|~m1_subset_1(X44,k1_zfmisc_1(u1_struct_0(X43)))))), inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc4_tmap_1])])])])).
% 0.20/0.43  cnf(c_0_81, negated_conjecture, (r1_tmap_1(X1,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),X1),esk8_0)|v2_struct_0(k6_tmap_1(esk5_0,esk6_0))|v2_struct_0(X1)|~m1_pre_topc(X1,esk5_0)|~m1_subset_1(esk8_0,u1_struct_0(X1))), inference(spm,[status(thm)],[c_0_78, c_0_79])).
% 0.20/0.43  cnf(c_0_82, negated_conjecture, (~r1_tmap_1(esk7_0,k6_tmap_1(esk5_0,esk6_0),k2_tmap_1(esk5_0,k6_tmap_1(esk5_0,esk6_0),k7_tmap_1(esk5_0,esk6_0),esk7_0),esk8_0)), inference(split_conjunct,[status(thm)],[c_0_19])).
% 0.20/0.43  cnf(c_0_83, plain, (v2_struct_0(X1)|~v2_struct_0(k6_tmap_1(X1,X2))|~v2_pre_topc(X1)|~l1_pre_topc(X1)|~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))), inference(split_conjunct,[status(thm)],[c_0_80])).
% 0.20/0.43  cnf(c_0_84, negated_conjecture, (v2_struct_0(k6_tmap_1(esk5_0,esk6_0))), inference(sr,[status(thm)],[inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_81, c_0_45]), c_0_25])]), c_0_82]), c_0_31])).
% 0.20/0.43  cnf(c_0_85, negated_conjecture, ($false), inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_83, c_0_84]), c_0_59]), c_0_26]), c_0_58])]), c_0_60]), ['proof']).
% 0.20/0.43  # SZS output end CNFRefutation
% 0.20/0.43  # Proof object total steps             : 86
% 0.20/0.43  # Proof object clause steps            : 55
% 0.20/0.43  # Proof object formula steps           : 31
% 0.20/0.43  # Proof object conjectures             : 36
% 0.20/0.43  # Proof object clause conjectures      : 33
% 0.20/0.43  # Proof object formula conjectures     : 3
% 0.20/0.43  # Proof object initial clauses used    : 28
% 0.20/0.43  # Proof object initial formulas used   : 15
% 0.20/0.43  # Proof object generating inferences   : 25
% 0.20/0.43  # Proof object simplifying inferences  : 55
% 0.20/0.43  # Training examples: 0 positive, 0 negative
% 0.20/0.43  # Parsed axioms                        : 17
% 0.20/0.43  # Removed by relevancy pruning/SinE    : 0
% 0.20/0.43  # Initial clauses                      : 40
% 0.20/0.43  # Removed in clause preprocessing      : 0
% 0.20/0.43  # Initial clauses in saturation        : 40
% 0.20/0.43  # Processed clauses                    : 409
% 0.20/0.43  # ...of these trivial                  : 3
% 0.20/0.43  # ...subsumed                          : 96
% 0.20/0.43  # ...remaining for further processing  : 310
% 0.20/0.43  # Other redundant clauses eliminated   : 3
% 0.20/0.43  # Clauses deleted for lack of memory   : 0
% 0.20/0.43  # Backward-subsumed                    : 8
% 0.20/0.43  # Backward-rewritten                   : 55
% 0.20/0.43  # Generated clauses                    : 698
% 0.20/0.43  # ...of the previous two non-trivial   : 674
% 0.20/0.43  # Contextual simplify-reflections      : 34
% 0.20/0.43  # Paramodulations                      : 693
% 0.20/0.43  # Factorizations                       : 0
% 0.20/0.43  # Equation resolutions                 : 3
% 0.20/0.43  # Propositional unsat checks           : 0
% 0.20/0.43  #    Propositional check models        : 0
% 0.20/0.43  #    Propositional check unsatisfiable : 0
% 0.20/0.43  #    Propositional clauses             : 0
% 0.20/0.43  #    Propositional clauses after purity: 0
% 0.20/0.43  #    Propositional unsat core size     : 0
% 0.20/0.43  #    Propositional preprocessing time  : 0.000
% 0.20/0.43  #    Propositional encoding time       : 0.000
% 0.20/0.43  #    Propositional solver time         : 0.000
% 0.20/0.43  #    Success case prop preproc time    : 0.000
% 0.20/0.43  #    Success case prop encoding time   : 0.000
% 0.20/0.43  #    Success case prop solver time     : 0.000
% 0.20/0.43  # Current number of processed clauses  : 242
% 0.20/0.43  #    Positive orientable unit clauses  : 40
% 0.20/0.43  #    Positive unorientable unit clauses: 0
% 0.20/0.43  #    Negative unit clauses             : 6
% 0.20/0.43  #    Non-unit-clauses                  : 196
% 0.20/0.43  # Current number of unprocessed clauses: 269
% 0.20/0.43  # ...number of literals in the above   : 1234
% 0.20/0.43  # Current number of archived formulas  : 0
% 0.20/0.43  # Current number of archived clauses   : 65
% 0.20/0.43  # Clause-clause subsumption calls (NU) : 17144
% 0.20/0.43  # Rec. Clause-clause subsumption calls : 8626
% 0.20/0.43  # Non-unit clause-clause subsumptions  : 120
% 0.20/0.43  # Unit Clause-clause subsumption calls : 788
% 0.20/0.43  # Rewrite failures with RHS unbound    : 0
% 0.20/0.43  # BW rewrite match attempts            : 12
% 0.20/0.43  # BW rewrite match successes           : 3
% 0.20/0.43  # Condensation attempts                : 0
% 0.20/0.43  # Condensation successes               : 0
% 0.20/0.43  # Termbank termtop insertions          : 26467
% 0.20/0.43  
% 0.20/0.43  # -------------------------------------------------
% 0.20/0.43  # User time                : 0.086 s
% 0.20/0.43  # System time              : 0.004 s
% 0.20/0.43  # Total time               : 0.090 s
% 0.20/0.43  # Maximum resident set size: 1600 pages
%------------------------------------------------------------------------------
