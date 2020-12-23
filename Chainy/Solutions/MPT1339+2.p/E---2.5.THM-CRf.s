%------------------------------------------------------------------------------
% File       : E---2.5
% Problem    : MPT1339+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : eprover --delete-bad-limit=2000000000 --definitional-cnf=24 -s --print-statistics -R --print-version --proof-object --auto-schedule --cpu-limit=%d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:05 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.12s
% Verified   : 
% Statistics : Number of formulae       :   31 (  61 expanded)
%              Number of clauses        :   18 (  21 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    7
%              Number of atoms          :   95 ( 314 expanded)
%              Number of equality atoms :   16 (  43 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(t63_tops_2,conjecture,(
    ! [X1] :
      ( l1_struct_0(X1)
     => ! [X2] :
          ( l1_struct_0(X2)
         => ! [X3] :
              ( ( v1_funct_1(X3)
                & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
             => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                  & v2_funct_1(X3) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

fof(d3_struct_0,axiom,(
    ! [X1] :
      ( l1_struct_0(X1)
     => k2_struct_0(X1) = u1_struct_0(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT016+2.ax',d3_struct_0)).

fof(cc2_relat_1,axiom,(
    ! [X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v1_relat_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',cc2_relat_1)).

fof(fc6_relat_1,axiom,(
    ! [X1,X2] : v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT007+2.ax',fc6_relat_1)).

fof(d4_tops_2,axiom,(
    ! [X1,X2,X3] :
      ( ( v1_funct_1(X3)
        & v1_funct_2(X3,X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
     => ( ( k2_relset_1(X1,X2,X3) = X2
          & v2_funct_1(X3) )
       => k2_tops_2(X1,X2,X3) = k2_funct_1(X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(fc6_funct_1,axiom,(
    ! [X1] :
      ( ( v1_relat_1(X1)
        & v1_funct_1(X1)
        & v2_funct_1(X1) )
     => ( v1_relat_1(k2_funct_1(X1))
        & v1_funct_1(k2_funct_1(X1))
        & v2_funct_1(k2_funct_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/Axioms/MPT008+2.ax',fc6_funct_1)).

fof(c_0_6,negated_conjecture,(
    ~ ! [X1] :
        ( l1_struct_0(X1)
       => ! [X2] :
            ( l1_struct_0(X2)
           => ! [X3] :
                ( ( v1_funct_1(X3)
                  & v1_funct_2(X3,u1_struct_0(X1),u1_struct_0(X2))
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) )
               => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X3) = k2_struct_0(X2)
                    & v2_funct_1(X3) )
                 => v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X3)) ) ) ) ) ),
    inference(assume_negation,[status(cth)],[t63_tops_2])).

fof(c_0_7,plain,(
    ! [X5896] :
      ( ~ l1_struct_0(X5896)
      | k2_struct_0(X5896) = u1_struct_0(X5896) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d3_struct_0])])).

fof(c_0_8,negated_conjecture,
    ( l1_struct_0(esk755_0)
    & l1_struct_0(esk756_0)
    & v1_funct_1(esk757_0)
    & v1_funct_2(esk757_0,u1_struct_0(esk755_0),u1_struct_0(esk756_0))
    & m1_subset_1(esk757_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0))))
    & k2_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_struct_0(esk756_0)
    & v2_funct_1(esk757_0)
    & ~ v2_funct_1(k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) ),
    inference(skolemize,[status(esa)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[c_0_6])])])).

cnf(c_0_9,plain,
    ( k2_struct_0(X1) = u1_struct_0(X1)
    | ~ l1_struct_0(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_7])).

cnf(c_0_10,negated_conjecture,
    ( l1_struct_0(esk756_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

fof(c_0_11,plain,(
    ! [X2097,X2098] :
      ( ~ v1_relat_1(X2097)
      | ~ m1_subset_1(X2098,k1_zfmisc_1(X2097))
      | v1_relat_1(X2098) ) ),
    inference(shift_quantors,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[cc2_relat_1])])])).

fof(c_0_12,plain,(
    ! [X2277,X2278] : v1_relat_1(k2_zfmisc_1(X2277,X2278)) ),
    inference(variable_rename,[status(thm)],[fc6_relat_1])).

fof(c_0_13,plain,(
    ! [X7101,X7102,X7103] :
      ( ~ v1_funct_1(X7103)
      | ~ v1_funct_2(X7103,X7101,X7102)
      | ~ m1_subset_1(X7103,k1_zfmisc_1(k2_zfmisc_1(X7101,X7102)))
      | k2_relset_1(X7101,X7102,X7103) != X7102
      | ~ v2_funct_1(X7103)
      | k2_tops_2(X7101,X7102,X7103) = k2_funct_1(X7103) ) ),
    inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[d4_tops_2])])).

cnf(c_0_14,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_struct_0(esk756_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_15,negated_conjecture,
    ( k2_struct_0(esk756_0) = u1_struct_0(esk756_0) ),
    inference(spm,[status(thm)],[c_0_9,c_0_10])).

fof(c_0_16,plain,(
    ! [X2808] :
      ( ( v1_relat_1(k2_funct_1(X2808))
        | ~ v1_relat_1(X2808)
        | ~ v1_funct_1(X2808)
        | ~ v2_funct_1(X2808) )
      & ( v1_funct_1(k2_funct_1(X2808))
        | ~ v1_relat_1(X2808)
        | ~ v1_funct_1(X2808)
        | ~ v2_funct_1(X2808) )
      & ( v2_funct_1(k2_funct_1(X2808))
        | ~ v1_relat_1(X2808)
        | ~ v1_funct_1(X2808)
        | ~ v2_funct_1(X2808) ) ) ),
    inference(distribute,[status(thm)],[inference(variable_rename,[status(thm)],[inference(fof_nnf,[status(thm)],[fc6_funct_1])])])).

cnf(c_0_17,plain,
    ( v1_relat_1(X2)
    | ~ v1_relat_1(X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) ),
    inference(split_conjunct,[status(thm)],[c_0_11])).

cnf(c_0_18,negated_conjecture,
    ( m1_subset_1(esk757_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0)))) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_19,plain,
    ( v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(split_conjunct,[status(thm)],[c_0_12])).

cnf(c_0_20,plain,
    ( k2_tops_2(X2,X3,X1) = k2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_2(X1,X2,X3)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | k2_relset_1(X2,X3,X1) != X3
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_13])).

cnf(c_0_21,negated_conjecture,
    ( k2_relset_1(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = u1_struct_0(esk756_0) ),
    inference(rw,[status(thm)],[c_0_14,c_0_15])).

cnf(c_0_22,negated_conjecture,
    ( v1_funct_2(esk757_0,u1_struct_0(esk755_0),u1_struct_0(esk756_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_23,negated_conjecture,
    ( v2_funct_1(esk757_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_24,negated_conjecture,
    ( v1_funct_1(esk757_0) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_25,plain,
    ( v2_funct_1(k2_funct_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1) ),
    inference(split_conjunct,[status(thm)],[c_0_16])).

cnf(c_0_26,negated_conjecture,
    ( v1_relat_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_17,c_0_18]),c_0_19])])).

cnf(c_0_27,negated_conjecture,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0)) ),
    inference(split_conjunct,[status(thm)],[c_0_8])).

cnf(c_0_28,negated_conjecture,
    ( k2_tops_2(u1_struct_0(esk755_0),u1_struct_0(esk756_0),esk757_0) = k2_funct_1(esk757_0) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_20,c_0_21]),c_0_22]),c_0_23]),c_0_24]),c_0_18])])).

cnf(c_0_29,negated_conjecture,
    ( v2_funct_1(k2_funct_1(esk757_0)) ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[inference(spm,[status(thm)],[c_0_25,c_0_24]),c_0_23]),c_0_26])])).

cnf(c_0_30,negated_conjecture,
    ( $false ),
    inference(cn,[status(thm)],[inference(rw,[status(thm)],[inference(rw,[status(thm)],[c_0_27,c_0_28]),c_0_29])]),
    [proof]).
%------------------------------------------------------------------------------
