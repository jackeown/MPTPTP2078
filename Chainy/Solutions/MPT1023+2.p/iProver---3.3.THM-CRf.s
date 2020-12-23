%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1023+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:08:59 EST 2020

% Result     : Theorem 55.08s
% Output     : CNFRefutation 55.08s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 102 expanded)
%              Number of clauses        :   19 (  19 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :  220 ( 785 expanded)
%              Number of equality atoms :   21 (  90 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1507,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( m1_subset_1(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1508,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( ! [X4] :
                  ( m1_subset_1(X4,X0)
                 => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
             => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    inference(negated_conjecture,[],[f1507])).

fof(f3118,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1508])).

fof(f3119,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f3118])).

fof(f4485,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_relset_1(X0,X1,X2,X3)
          & ! [X4] :
              ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,X0) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_relset_1(X0,X1,X2,sK529)
        & ! [X4] :
            ( k1_funct_1(sK529,X4) = k1_funct_1(X2,X4)
            | ~ m1_subset_1(X4,X0) )
        & m1_subset_1(sK529,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK529,X0,X1)
        & v1_funct_1(sK529) ) ) ),
    introduced(choice_axiom,[])).

fof(f4484,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_relset_1(X0,X1,X2,X3)
            & ! [X4] :
                ( k1_funct_1(X2,X4) = k1_funct_1(X3,X4)
                | ~ m1_subset_1(X4,X0) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_relset_1(sK526,sK527,sK528,X3)
          & ! [X4] :
              ( k1_funct_1(sK528,X4) = k1_funct_1(X3,X4)
              | ~ m1_subset_1(X4,sK526) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527)))
          & v1_funct_2(X3,sK526,sK527)
          & v1_funct_1(X3) )
      & m1_subset_1(sK528,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527)))
      & v1_funct_2(sK528,sK526,sK527)
      & v1_funct_1(sK528) ) ),
    introduced(choice_axiom,[])).

fof(f4486,plain,
    ( ~ r2_relset_1(sK526,sK527,sK528,sK529)
    & ! [X4] :
        ( k1_funct_1(sK528,X4) = k1_funct_1(sK529,X4)
        | ~ m1_subset_1(X4,sK526) )
    & m1_subset_1(sK529,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527)))
    & v1_funct_2(sK529,sK526,sK527)
    & v1_funct_1(sK529)
    & m1_subset_1(sK528,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527)))
    & v1_funct_2(sK528,sK526,sK527)
    & v1_funct_1(sK528) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK526,sK527,sK528,sK529])],[f3119,f4485,f4484])).

fof(f7351,plain,(
    ! [X4] :
      ( k1_funct_1(sK528,X4) = k1_funct_1(sK529,X4)
      | ~ m1_subset_1(X4,sK526) ) ),
    inference(cnf_transformation,[],[f4486])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f1972,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f5479,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1972])).

fof(f1513,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ! [X4] :
                ( r2_hidden(X4,X0)
               => k1_funct_1(X2,X4) = k1_funct_1(X3,X4) )
           => r2_relset_1(X0,X1,X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f3128,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1513])).

fof(f3129,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ? [X4] :
              ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
              & r2_hidden(X4,X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f3128])).

fof(f4491,plain,(
    ! [X3,X2,X0] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) != k1_funct_1(X3,X4)
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK532(X0,X2,X3)) != k1_funct_1(X3,sK532(X0,X2,X3))
        & r2_hidden(sK532(X0,X2,X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f4492,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r2_relset_1(X0,X1,X2,X3)
          | ( k1_funct_1(X2,sK532(X0,X2,X3)) != k1_funct_1(X3,sK532(X0,X2,X3))
            & r2_hidden(sK532(X0,X2,X3),X0) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK532])],[f3129,f4491])).

fof(f7361,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | k1_funct_1(X2,sK532(X0,X2,X3)) != k1_funct_1(X3,sK532(X0,X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f4492])).

fof(f7360,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | r2_hidden(sK532(X0,X2,X3),X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f4492])).

fof(f1239,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
       => r2_relset_1(X0,X1,X3,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f2848,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1239])).

fof(f2849,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f2848])).

fof(f6659,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X2)
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2849])).

fof(f7352,plain,(
    ~ r2_relset_1(sK526,sK527,sK528,sK529) ),
    inference(cnf_transformation,[],[f4486])).

fof(f7350,plain,(
    m1_subset_1(sK529,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527))) ),
    inference(cnf_transformation,[],[f4486])).

fof(f7349,plain,(
    v1_funct_2(sK529,sK526,sK527) ),
    inference(cnf_transformation,[],[f4486])).

fof(f7348,plain,(
    v1_funct_1(sK529) ),
    inference(cnf_transformation,[],[f4486])).

fof(f7347,plain,(
    m1_subset_1(sK528,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527))) ),
    inference(cnf_transformation,[],[f4486])).

fof(f7346,plain,(
    v1_funct_2(sK528,sK526,sK527) ),
    inference(cnf_transformation,[],[f4486])).

fof(f7345,plain,(
    v1_funct_1(sK528) ),
    inference(cnf_transformation,[],[f4486])).

cnf(c_2794,negated_conjecture,
    ( ~ m1_subset_1(X0,sK526)
    | k1_funct_1(sK528,X0) = k1_funct_1(sK529,X0) ),
    inference(cnf_transformation,[],[f7351])).

cnf(c_194512,plain,
    ( ~ m1_subset_1(sK532(sK526,sK529,sK528),sK526)
    | k1_funct_1(sK528,sK532(sK526,sK529,sK528)) = k1_funct_1(sK529,sK532(sK526,sK529,sK528)) ),
    inference(instantiation,[status(thm)],[c_2794])).

cnf(c_937,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f5479])).

cnf(c_145026,plain,
    ( m1_subset_1(X0,sK526)
    | ~ r2_hidden(X0,sK526) ),
    inference(instantiation,[status(thm)],[c_937])).

cnf(c_167285,plain,
    ( m1_subset_1(sK532(sK526,sK529,sK528),sK526)
    | ~ r2_hidden(sK532(sK526,sK529,sK528),sK526) ),
    inference(instantiation,[status(thm)],[c_145026])).

cnf(c_2808,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k1_funct_1(X3,sK532(X0,X2,X3)) != k1_funct_1(X2,sK532(X0,X2,X3)) ),
    inference(cnf_transformation,[],[f7361])).

cnf(c_146451,plain,
    ( r2_relset_1(sK526,sK527,sK529,sK528)
    | ~ v1_funct_2(sK529,sK526,sK527)
    | ~ v1_funct_2(sK528,sK526,sK527)
    | ~ m1_subset_1(sK529,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527)))
    | ~ m1_subset_1(sK528,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527)))
    | ~ v1_funct_1(sK529)
    | ~ v1_funct_1(sK528)
    | k1_funct_1(sK528,sK532(sK526,sK529,sK528)) != k1_funct_1(sK529,sK532(sK526,sK529,sK528)) ),
    inference(instantiation,[status(thm)],[c_2808])).

cnf(c_2809,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK532(X0,X2,X3),X0)
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f7360])).

cnf(c_146454,plain,
    ( r2_relset_1(sK526,sK527,sK529,sK528)
    | ~ v1_funct_2(sK529,sK526,sK527)
    | ~ v1_funct_2(sK528,sK526,sK527)
    | ~ m1_subset_1(sK529,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527)))
    | ~ m1_subset_1(sK528,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527)))
    | r2_hidden(sK532(sK526,sK529,sK528),sK526)
    | ~ v1_funct_1(sK529)
    | ~ v1_funct_1(sK528) ),
    inference(instantiation,[status(thm)],[c_2809])).

cnf(c_2116,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X0,X1,X3,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f6659])).

cnf(c_144978,plain,
    ( ~ r2_relset_1(sK526,sK527,sK529,sK528)
    | r2_relset_1(sK526,sK527,sK528,sK529)
    | ~ m1_subset_1(sK529,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527)))
    | ~ m1_subset_1(sK528,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527))) ),
    inference(instantiation,[status(thm)],[c_2116])).

cnf(c_2793,negated_conjecture,
    ( ~ r2_relset_1(sK526,sK527,sK528,sK529) ),
    inference(cnf_transformation,[],[f7352])).

cnf(c_2795,negated_conjecture,
    ( m1_subset_1(sK529,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527))) ),
    inference(cnf_transformation,[],[f7350])).

cnf(c_2796,negated_conjecture,
    ( v1_funct_2(sK529,sK526,sK527) ),
    inference(cnf_transformation,[],[f7349])).

cnf(c_2797,negated_conjecture,
    ( v1_funct_1(sK529) ),
    inference(cnf_transformation,[],[f7348])).

cnf(c_2798,negated_conjecture,
    ( m1_subset_1(sK528,k1_zfmisc_1(k2_zfmisc_1(sK526,sK527))) ),
    inference(cnf_transformation,[],[f7347])).

cnf(c_2799,negated_conjecture,
    ( v1_funct_2(sK528,sK526,sK527) ),
    inference(cnf_transformation,[],[f7346])).

cnf(c_2800,negated_conjecture,
    ( v1_funct_1(sK528) ),
    inference(cnf_transformation,[],[f7345])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_194512,c_167285,c_146451,c_146454,c_144978,c_2793,c_2795,c_2796,c_2797,c_2798,c_2799,c_2800])).

%------------------------------------------------------------------------------
