%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1876+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:41:57 EST 2020

% Result     : Theorem 0.20s
% Output     : CNFRefutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 (1256 expanded)
%              Number of clauses        :   66 ( 495 expanded)
%              Number of leaves         :   19 ( 313 expanded)
%              Depth                    :   18
%              Number of atoms          :  314 (6058 expanded)
%              Number of equality atoms :   53 ( 377 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   23 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t44_tex_2,conjecture,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & v2_tdlat_3(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( ( ~ v1_xboole_0(X2)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
         => ( v2_tex_2(X2,X1)
          <=> v1_zfmisc_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(redefinition_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k3_xboole_0(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(t32_tex_2,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
         => ( v2_tex_2(X2,X1)
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X1))
               => ~ ( r2_hidden(X3,X2)
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
                       => ~ ( v3_pre_topc(X4,X1)
                            & k9_subset_1(u1_struct_0(X1),X2,X4) = k1_tarski(X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_tex_2)).

fof(t4_subset,axiom,(
    ! [X1,X2,X3] :
      ( ( r2_hidden(X1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(X3)) )
     => m1_subset_1(X1,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(commutativity_k9_subset_1,axiom,(
    ! [X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(X1))
     => k9_subset_1(X1,X2,X3) = k9_subset_1(X1,X3,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(commutativity_k3_xboole_0,axiom,(
    ! [X1,X2] : k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(t2_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,X2)
     => ( v1_xboole_0(X2)
        | r2_hidden(X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(existence_m1_subset_1,axiom,(
    ! [X1] :
    ? [X2] : m1_subset_1(X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(t3_subset,axiom,(
    ! [X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X2))
    <=> r1_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(t20_tdlat_3,axiom,(
    ! [X1] :
      ( ( v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ( v2_tdlat_3(X1)
      <=> ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
           => ~ ( v3_pre_topc(X2,X1)
                & X2 != k1_xboole_0
                & X2 != u1_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tdlat_3)).

fof(t28_xboole_1,axiom,(
    ! [X1,X2] :
      ( r1_tarski(X1,X2)
     => k3_xboole_0(X1,X2) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(redefinition_k6_domain_1,axiom,(
    ! [X1,X2] :
      ( ( ~ v1_xboole_0(X1)
        & m1_subset_1(X2,X1) )
     => k6_domain_1(X1,X2) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(d1_tex_2,axiom,(
    ! [X1] :
      ( ~ v1_xboole_0(X1)
     => ( v1_zfmisc_1(X1)
      <=> ? [X2] :
            ( m1_subset_1(X2,X1)
            & X1 = k6_domain_1(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

fof(t2_boole,axiom,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(fc2_xboole_0,axiom,(
    ! [X1] : ~ v1_xboole_0(k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(fc1_xboole_0,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(t36_tex_2,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & v2_pre_topc(X1)
        & l1_pre_topc(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_tex_2)).

fof(dt_l1_pre_topc,axiom,(
    ! [X1] :
      ( l1_pre_topc(X1)
     => l1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(fc2_struct_0,axiom,(
    ! [X1] :
      ( ( ~ v2_struct_0(X1)
        & l1_struct_0(X1) )
     => ~ v1_xboole_0(u1_struct_0(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(c_0_19,negated_conjecture,(
    ~ ! [X1] :
        ( ( ~ v2_struct_0(X1)
          & v2_pre_topc(X1)
          & v2_tdlat_3(X1)
          & l1_pre_topc(X1) )
       => ! [X2] :
            ( ( ~ v1_xboole_0(X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
           => ( v2_tex_2(X2,X1)
            <=> v1_zfmisc_1(X2) ) ) ) ),
    inference(assume_negation,[status(cth)],[t44_tex_2])).

fof(c_0_20,plain,(
    ! [X27,X28,X29] :
      ( ~ m1_subset_1(X29,k1_zfmisc_1(X27))
      | k9_subset_1(X27,X28,X29) = k3_xboole_0(X28,X29) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[redefinition_k9_subset_1])])).

fof(c_0_21,negated_conjecture,
    ( ~ v2_struct_0(esk6_0)
    & v2_pre_topc(esk6_0)
    & v2_tdlat_3(esk6_0)
    & l1_pre_topc(esk6_0)
    & ~ v1_xboole_0(esk7_0)
    & m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0)))
    & ( ~ v2_tex_2(esk7_0,esk6_0)
      | ~ v1_zfmisc_1(esk7_0) )
    & ( v2_tex_2(esk7_0,esk6_0)
      | v1_zfmisc_1(esk7_0) ) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[c_0_19])])])])).

fof(c_0_22,plain,(
    ! [X38,X39,X40] :
      ( ( m1_subset_1(esk5_3(X38,X39,X40),k1_zfmisc_1(u1_struct_0(X38)))
        | ~ r2_hidden(X40,X39)
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ v2_tex_2(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) )
      & ( v3_pre_topc(esk5_3(X38,X39,X40),X38)
        | ~ r2_hidden(X40,X39)
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ v2_tex_2(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) )
      & ( k9_subset_1(u1_struct_0(X38),X39,esk5_3(X38,X39,X40)) = k1_tarski(X40)
        | ~ r2_hidden(X40,X39)
        | ~ m1_subset_1(X40,u1_struct_0(X38))
        | ~ v2_tex_2(X39,X38)
        | ~ m1_subset_1(X39,k1_zfmisc_1(u1_struct_0(X38)))
        | ~ l1_pre_topc(X38) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t32_tex_2])])])])])).

fof(c_0_23,plain,(
    ! [X46,X47,X48] :
      ( ~ r2_hidden(X46,X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(X48))
      | m1_subset_1(X46,X48) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t4_subset])])).

fof(c_0_24,plain,(
    ! [X7,X8,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(X7))
      | k9_subset_1(X7,X8,X9) = k9_subset_1(X7,X9,X8) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[commutativity_k9_subset_1])])).

cnf(c_0_25,plain,
    ( k9_subset_1(X2,X3,X1) = k3_xboole_0(X3,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_20])).

cnf(c_0_26,negated_conjecture,
    ( m1_subset_1(esk7_0,k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_27,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_28,plain,
    ( m1_subset_1(X1,X3)
    | ~ r2_hidden(X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ),
    inference(split_conjunct,[status(thm)],[c_0_23])).

cnf(c_0_29,plain,
    ( v3_pre_topc(esk5_3(X1,X2,X3),X1)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_30,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk5_3(X1,X2,X3)) = k1_tarski(X3)
    | ~ r2_hidden(X3,X2)
    | ~ m1_subset_1(X3,u1_struct_0(X1))
    | ~ v2_tex_2(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_22])).

cnf(c_0_31,plain,
    ( k9_subset_1(X2,X3,X1) = k9_subset_1(X2,X1,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_24])).

cnf(c_0_32,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),X1,esk7_0) = k3_xboole_0(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_25,c_0_26])).

fof(c_0_33,plain,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k3_xboole_0(X6,X5) ),
    inference(variable_rename,[status(thm)],[commutativity_k3_xboole_0])).

cnf(c_0_34,plain,
    ( m1_subset_1(esk5_3(X1,X2,X3),k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v2_tex_2(X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_27,c_0_28])).

cnf(c_0_35,negated_conjecture,
    ( l1_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_36,plain,(
    ! [X36,X37] :
      ( ~ m1_subset_1(X36,X37)
      | v1_xboole_0(X37)
      | r2_hidden(X36,X37) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t2_subset])])).

fof(c_0_37,plain,(
    ! [X19] : m1_subset_1(esk2_1(X19),X19) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[existence_m1_subset_1])])).

cnf(c_0_38,plain,
    ( v3_pre_topc(esk5_3(X1,X2,X3),X1)
    | ~ v2_tex_2(X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_29,c_0_28])).

cnf(c_0_39,plain,
    ( k9_subset_1(u1_struct_0(X1),X2,esk5_3(X1,X2,X3)) = k1_tarski(X3)
    | ~ v2_tex_2(X2,X1)
    | ~ r2_hidden(X3,X2)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) ),
    inference(csr,[status(thm)],[c_0_30,c_0_28])).

cnf(c_0_40,negated_conjecture,
    ( k9_subset_1(u1_struct_0(esk6_0),esk7_0,X1) = k3_xboole_0(X1,esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_31,c_0_26]),c_0_32])).

cnf(c_0_41,plain,
    ( k3_xboole_0(X1,X2) = k3_xboole_0(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_33])).

cnf(c_0_42,negated_conjecture,
    ( m1_subset_1(esk5_3(esk6_0,esk7_0,X1),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ v2_tex_2(esk7_0,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_34,c_0_26]),c_0_35])])).

cnf(c_0_43,negated_conjecture,
    ( v2_tex_2(esk7_0,esk6_0)
    | v1_zfmisc_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_44,plain,
    ( v1_xboole_0(X2)
    | r2_hidden(X1,X2)
    | ~ m1_subset_1(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_36])).

cnf(c_0_45,plain,
    ( m1_subset_1(esk2_1(X1),X1) ),
    inference(split_conjunct,[status(thm)],[c_0_37])).

cnf(c_0_46,negated_conjecture,
    ( v3_pre_topc(esk5_3(esk6_0,esk7_0,X1),esk6_0)
    | ~ v2_tex_2(esk7_0,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_38,c_0_26]),c_0_35])])).

fof(c_0_47,plain,(
    ! [X44,X45] :
      ( ( ~ m1_subset_1(X44,k1_zfmisc_1(X45))
        | r1_tarski(X44,X45) )
      & ( ~ r1_tarski(X44,X45)
        | m1_subset_1(X44,k1_zfmisc_1(X45)) ) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t3_subset])])).

cnf(c_0_48,negated_conjecture,
    ( k3_xboole_0(esk7_0,esk5_3(esk6_0,esk7_0,X1)) = k1_tarski(X1)
    | ~ v2_tex_2(esk7_0,esk6_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_39,c_0_26]),c_0_35])]),c_0_40]),c_0_41])).

fof(c_0_49,plain,(
    ! [X30,X31] :
      ( ( ~ v2_tdlat_3(X30)
        | ~ m1_subset_1(X31,k1_zfmisc_1(u1_struct_0(X30)))
        | ~ v3_pre_topc(X31,X30)
        | X31 = k1_xboole_0
        | X31 = u1_struct_0(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( m1_subset_1(esk4_1(X30),k1_zfmisc_1(u1_struct_0(X30)))
        | v2_tdlat_3(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( v3_pre_topc(esk4_1(X30),X30)
        | v2_tdlat_3(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( esk4_1(X30) != k1_xboole_0
        | v2_tdlat_3(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) )
      & ( esk4_1(X30) != u1_struct_0(X30)
        | v2_tdlat_3(X30)
        | ~ v2_pre_topc(X30)
        | ~ l1_pre_topc(X30) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t20_tdlat_3])])])])])).

cnf(c_0_50,negated_conjecture,
    ( v1_zfmisc_1(esk7_0)
    | m1_subset_1(esk5_3(esk6_0,esk7_0,X1),k1_zfmisc_1(u1_struct_0(esk6_0)))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_42,c_0_43])).

cnf(c_0_51,plain,
    ( r2_hidden(esk2_1(X1),X1)
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_44,c_0_45])).

cnf(c_0_52,negated_conjecture,
    ( ~ v1_xboole_0(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_53,negated_conjecture,
    ( v3_pre_topc(esk5_3(esk6_0,esk7_0,X1),esk6_0)
    | v1_zfmisc_1(esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_46,c_0_43])).

fof(c_0_54,plain,(
    ! [X33,X34] :
      ( ~ r1_tarski(X33,X34)
      | k3_xboole_0(X33,X34) = X33 ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[t28_xboole_1])])).

cnf(c_0_55,plain,
    ( r1_tarski(X1,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_47])).

fof(c_0_56,plain,(
    ! [X25,X26] :
      ( v1_xboole_0(X25)
      | ~ m1_subset_1(X26,X25)
      | k6_domain_1(X25,X26) = k1_tarski(X26) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[redefinition_k6_domain_1])])])).

cnf(c_0_57,negated_conjecture,
    ( k3_xboole_0(esk7_0,esk5_3(esk6_0,esk7_0,X1)) = k1_tarski(X1)
    | v1_zfmisc_1(esk7_0)
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_48,c_0_43])).

cnf(c_0_58,plain,
    ( X2 = k1_xboole_0
    | X2 = u1_struct_0(X1)
    | ~ v2_tdlat_3(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
    | ~ v3_pre_topc(X2,X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_49])).

cnf(c_0_59,negated_conjecture,
    ( v1_zfmisc_1(esk7_0)
    | m1_subset_1(esk5_3(esk6_0,esk7_0,esk2_1(esk7_0)),k1_zfmisc_1(u1_struct_0(esk6_0))) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_50,c_0_51]),c_0_52])).

cnf(c_0_60,negated_conjecture,
    ( v2_tdlat_3(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_61,negated_conjecture,
    ( v2_pre_topc(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_62,negated_conjecture,
    ( v3_pre_topc(esk5_3(esk6_0,esk7_0,esk2_1(esk7_0)),esk6_0)
    | v1_zfmisc_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_53,c_0_51]),c_0_52])).

cnf(c_0_63,plain,
    ( k3_xboole_0(X1,X2) = X1
    | ~ r1_tarski(X1,X2) ),
    inference(split_conjunct,[status(thm)],[c_0_54])).

cnf(c_0_64,negated_conjecture,
    ( r1_tarski(esk7_0,u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_55,c_0_26])).

fof(c_0_65,plain,(
    ! [X10,X12] :
      ( ( m1_subset_1(esk1_1(X10),X10)
        | ~ v1_zfmisc_1(X10)
        | v1_xboole_0(X10) )
      & ( X10 = k6_domain_1(X10,esk1_1(X10))
        | ~ v1_zfmisc_1(X10)
        | v1_xboole_0(X10) )
      & ( ~ m1_subset_1(X12,X10)
        | X10 != k6_domain_1(X10,X12)
        | v1_zfmisc_1(X10)
        | v1_xboole_0(X10) ) ) ),
    inference(distribute,[status(thm)],[inference(shift_quantors,[status(thm)],[inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[d1_tex_2])])])])])])).

cnf(c_0_66,plain,
    ( v1_xboole_0(X1)
    | k6_domain_1(X1,X2) = k1_tarski(X2)
    | ~ m1_subset_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_56])).

cnf(c_0_67,negated_conjecture,
    ( k3_xboole_0(esk7_0,esk5_3(esk6_0,esk7_0,esk2_1(esk7_0))) = k1_tarski(esk2_1(esk7_0))
    | v1_zfmisc_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_57,c_0_51]),c_0_52])).

cnf(c_0_68,negated_conjecture,
    ( esk5_3(esk6_0,esk7_0,esk2_1(esk7_0)) = u1_struct_0(esk6_0)
    | esk5_3(esk6_0,esk7_0,esk2_1(esk7_0)) = k1_xboole_0
    | v1_zfmisc_1(esk7_0) ),
    inference(csr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_58,c_0_59]),c_0_60]),c_0_61]),c_0_35])]),c_0_62])).

cnf(c_0_69,negated_conjecture,
    ( k3_xboole_0(esk7_0,u1_struct_0(esk6_0)) = esk7_0 ),
    inference(spm,[status(thm)],[c_0_63,c_0_64])).

fof(c_0_70,plain,(
    ! [X35] : k3_xboole_0(X35,k1_xboole_0) = k1_xboole_0 ),
    inference(variable_rename,[status(thm)],[t2_boole])).

cnf(c_0_71,plain,
    ( v1_zfmisc_1(X2)
    | v1_xboole_0(X2)
    | ~ m1_subset_1(X1,X2)
    | X2 != k6_domain_1(X2,X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_72,plain,
    ( k6_domain_1(X1,esk2_1(X1)) = k1_tarski(esk2_1(X1))
    | v1_xboole_0(X1) ),
    inference(spm,[status(thm)],[c_0_66,c_0_45])).

cnf(c_0_73,negated_conjecture,
    ( esk5_3(esk6_0,esk7_0,esk2_1(esk7_0)) = k1_xboole_0
    | k1_tarski(esk2_1(esk7_0)) = esk7_0
    | v1_zfmisc_1(esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_68]),c_0_69])).

cnf(c_0_74,plain,
    ( k3_xboole_0(X1,k1_xboole_0) = k1_xboole_0 ),
    inference(split_conjunct,[status(thm)],[c_0_70])).

fof(c_0_75,plain,(
    ! [X22] : ~ v1_xboole_0(k1_tarski(X22)) ),
    inference(variable_rename,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_xboole_0])])).

cnf(c_0_76,plain,
    ( v1_zfmisc_1(X1)
    | v1_xboole_0(X1)
    | k1_tarski(esk2_1(X1)) != X1 ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_71,c_0_72]),c_0_45])])).

cnf(c_0_77,negated_conjecture,
    ( k1_tarski(esk2_1(esk7_0)) = esk7_0
    | k1_tarski(esk2_1(esk7_0)) = k1_xboole_0
    | v1_zfmisc_1(esk7_0) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_67,c_0_73]),c_0_74])).

cnf(c_0_78,plain,
    ( ~ v1_xboole_0(k1_tarski(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_75])).

cnf(c_0_79,negated_conjecture,
    ( k1_tarski(esk2_1(esk7_0)) = k1_xboole_0
    | v1_zfmisc_1(esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_76,c_0_77]),c_0_52])).

cnf(c_0_80,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(split_conjunct,[status(thm)],[fc1_xboole_0])).

cnf(c_0_81,plain,
    ( m1_subset_1(esk1_1(X1),X1)
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

cnf(c_0_82,negated_conjecture,
    ( v1_zfmisc_1(esk7_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_78,c_0_79]),c_0_80])])).

cnf(c_0_83,negated_conjecture,
    ( m1_subset_1(esk1_1(esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_81,c_0_82]),c_0_52])).

cnf(c_0_84,plain,
    ( X1 = k6_domain_1(X1,esk1_1(X1))
    | v1_xboole_0(X1)
    | ~ v1_zfmisc_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_65])).

fof(c_0_85,plain,(
    ! [X42,X43] :
      ( v2_struct_0(X42)
      | ~ v2_pre_topc(X42)
      | ~ l1_pre_topc(X42)
      | ~ m1_subset_1(X43,u1_struct_0(X42))
      | v2_tex_2(k6_domain_1(u1_struct_0(X42),X43),X42) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[t36_tex_2])])])])).

cnf(c_0_86,negated_conjecture,
    ( m1_subset_1(X1,u1_struct_0(esk6_0))
    | ~ r2_hidden(X1,esk7_0) ),
    inference(spm,[status(thm)],[c_0_28,c_0_26])).

cnf(c_0_87,negated_conjecture,
    ( r2_hidden(esk1_1(esk7_0),esk7_0) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_44,c_0_83]),c_0_52])).

cnf(c_0_88,negated_conjecture,
    ( k6_domain_1(esk7_0,esk1_1(esk7_0)) = esk7_0 ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_84,c_0_82]),c_0_52])).

cnf(c_0_89,plain,
    ( v2_struct_0(X1)
    | v2_tex_2(k6_domain_1(u1_struct_0(X1),X2),X1)
    | ~ v2_pre_topc(X1)
    | ~ l1_pre_topc(X1)
    | ~ m1_subset_1(X2,u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_85])).

cnf(c_0_90,negated_conjecture,
    ( m1_subset_1(esk1_1(esk7_0),u1_struct_0(esk6_0)) ),
    inference(spm,[status(thm)],[c_0_86,c_0_87])).

cnf(c_0_91,negated_conjecture,
    ( ~ v2_struct_0(esk6_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

cnf(c_0_92,negated_conjecture,
    ( k1_tarski(esk1_1(esk7_0)) = esk7_0 ),
    inference(rw,[status(thm)],[inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_83]),c_0_52]),c_0_88])).

cnf(c_0_93,negated_conjecture,
    ( ~ v2_tex_2(esk7_0,esk6_0)
    | ~ v1_zfmisc_1(esk7_0) ),
    inference(split_conjunct,[status(thm)],[c_0_21])).

fof(c_0_94,plain,(
    ! [X18] :
      ( ~ l1_pre_topc(X18)
      | l1_struct_0(X18) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[dt_l1_pre_topc])])).

fof(c_0_95,plain,(
    ! [X21] :
      ( v2_struct_0(X21)
      | ~ l1_struct_0(X21)
      | ~ v1_xboole_0(u1_struct_0(X21)) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[inference(fof_simplification,[status(thm)],[fc2_struct_0])])])).

cnf(c_0_96,negated_conjecture,
    ( v2_tex_2(k6_domain_1(u1_struct_0(esk6_0),esk1_1(esk7_0)),esk6_0) ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_89,c_0_90]),c_0_61]),c_0_35])]),c_0_91])).

cnf(c_0_97,negated_conjecture,
    ( k6_domain_1(u1_struct_0(esk6_0),esk1_1(esk7_0)) = esk7_0
    | v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_66,c_0_90]),c_0_92])).

cnf(c_0_98,negated_conjecture,
    ( ~ v2_tex_2(esk7_0,esk6_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[c_0_93,c_0_82])])).

cnf(c_0_99,plain,
    ( l1_struct_0(X1)
    | ~ l1_pre_topc(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_94])).

cnf(c_0_100,plain,
    ( v2_struct_0(X1)
    | ~ l1_struct_0(X1)
    | ~ v1_xboole_0(u1_struct_0(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_95])).

cnf(c_0_101,negated_conjecture,
    ( v1_xboole_0(u1_struct_0(esk6_0)) ),
    inference(sr,[status(thm)],[inference(spm,[status(thm)],[c_0_96,c_0_97]),c_0_98])).

cnf(c_0_102,negated_conjecture,
    ( l1_struct_0(esk6_0) ),
    inference(spm,[status(thm)],[c_0_99,c_0_35])).

cnf(c_0_103,negated_conjecture,
    ( $false ),
    inference(sr,[status(thm)],[inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_100,c_0_101]),c_0_102])]),c_0_91]),
    [proof]).

%------------------------------------------------------------------------------
