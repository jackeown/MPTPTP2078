%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9DpKy2adAI

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:06:08 EST 2020

% Result     : Theorem 0.83s
% Output     : Refutation 0.83s
% Verified   : 
% Statistics : Number of formulae       :  374 (1829 expanded)
%              Number of leaves         :   48 ( 552 expanded)
%              Depth                    :   37
%              Number of atoms          : 4389 (38437 expanded)
%              Number of equality atoms :  269 (1357 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tops_2_type,type,(
    k2_tops_2: $i > $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t64_tops_2,conjecture,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                    = ( k2_struct_0 @ B ) )
                  & ( v2_funct_1 @ C ) )
               => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_struct_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
               => ( ( ( ( k2_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C )
                      = ( k2_struct_0 @ B ) )
                    & ( v2_funct_1 @ C ) )
                 => ( r2_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( k2_tops_2 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ ( k2_tops_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_tops_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('4',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X33: $i] :
      ( ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('11',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ( ( k5_relat_1 @ X31 @ ( k2_funct_1 @ X31 ) )
        = ( k6_partfun1 @ X32 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X32 @ X30 @ X31 )
       != X30 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t48_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) ) )
           => ( ( v2_funct_1 @ B )
              & ( v2_funct_1 @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k5_relat_1 @ X0 @ ( k2_funct_1 @ X0 ) )
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t64_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ B )
                = ( k1_relat_1 @ A ) )
              & ( ( k5_relat_1 @ B @ A )
                = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('34',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X6 @ X7 )
       != ( k6_relat_1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_funct_1])).

thf('35',plain,(
    ! [X19: $i] :
      ( ( k6_partfun1 @ X19 )
      = ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ( X6
        = ( k2_funct_1 @ X7 ) )
      | ( ( k5_relat_1 @ X6 @ X7 )
       != ( k6_partfun1 @ ( k2_relat_1 @ X7 ) ) )
      | ( ( k2_relat_1 @ X6 )
       != ( k1_relat_1 @ X7 ) )
      | ~ ( v2_funct_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k6_partfun1 @ ( k1_relat_1 @ X0 ) )
       != ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
       != ( k1_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['1','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('52',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('58',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('59',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['55','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k1_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','66'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('68',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('70',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( X24 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X24 )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('71',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X26 @ X24 )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( v1_partfun1 @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('76',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('77',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('79',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('80',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('82',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('83',plain,(
    v4_relat_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( u1_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['77','80','83'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('85',plain,(
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('86',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('87',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('88',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k1_relat_1 @ sk_C )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['68','91'])).

thf('93',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['78','79'])).

thf('96',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['67','94','95','96','97'])).

thf('99',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v1_relat_1 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('100',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('105',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('108',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('109',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('110',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v4_relat_1 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['108','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['105','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['104','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['103','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['102','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('127',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k1_relat_1 @ X5 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('130',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('132',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ X18 )
       != X17 )
      | ( v1_partfun1 @ X18 @ X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('133',plain,(
    ! [X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v4_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) )
      | ( v1_partfun1 @ X18 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['131','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['130','135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['128','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['127','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['126','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['124','145'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v4_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['123','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','151'])).

thf('153',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ~ ( v2_funct_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','152'])).

thf('154',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('155',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('156',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['78','79'])).

thf('159',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('160',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('161',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['159','164'])).

thf('166',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('168',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v2_funct_1 @ X27 )
      | ( ( k2_relset_1 @ X29 @ X28 @ X27 )
       != X28 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('169',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('172',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('173',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['172','173'])).

thf('175',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('177',plain,
    ( ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['171','176'])).

thf('178',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('181',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('182',plain,
    ( ( k2_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['181','182'])).

thf('184',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_struct_0 @ sk_B ) )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['180','185'])).

thf('187',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['169','170','179','188','189'])).

thf('191',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( ( k1_relat_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
      = ( k2_struct_0 @ sk_A ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['153','154','155','156','157','158','191'])).

thf('193',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['49','192'])).

thf('194',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('195',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('196',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['193','194','195'])).

thf('197',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('198',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ( ( k5_relat_1 @ X31 @ ( k2_funct_1 @ X31 ) )
        = ( k6_partfun1 @ X32 ) )
      | ~ ( v2_funct_1 @ X31 )
      | ( ( k2_relset_1 @ X32 @ X30 @ X31 )
       != X30 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('199',plain,
    ( ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('201',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('203',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['199','200','201','202','203'])).

thf('205',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['204'])).

thf('206',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v2_funct_1 @ X4 )
      | ( ( k2_relat_1 @ X3 )
       != ( k1_relat_1 @ X4 ) )
      | ~ ( v2_funct_1 @ ( k5_relat_1 @ X3 @ X4 ) )
      | ~ ( v1_funct_1 @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t48_funct_1])).

thf('207',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ ( k2_struct_0 @ sk_A ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X2 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('209',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('210',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['190'])).

thf('211',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('212',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('213',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('214',plain,(
    ! [X0: $i] :
      ( ( v1_partfun1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('215',plain,
    ( ( v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['213','214'])).

thf('216',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['78','79'])).

thf('217',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_partfun1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['215','216','217','218'])).

thf('220',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_partfun1 @ X18 @ X17 )
      | ( ( k1_relat_1 @ X18 )
        = X17 )
      | ~ ( v4_relat_1 @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('221',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('224',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['78','79'])).

thf('226',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['224','225','226','227'])).

thf('229',plain,
    ( ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['221','228'])).

thf('230',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['212','229'])).

thf('231',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['78','79'])).

thf('232',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['230','231','232'])).

thf('234',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['78','79'])).

thf('236',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) )
    | ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['207','208','209','210','211','233','234','235'])).

thf('237',plain,
    ( ( v2_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) )
      = ( k2_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['196','237'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('240',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('242',plain,(
    ! [X5: $i] :
      ( ~ ( v2_funct_1 @ X5 )
      | ( ( k2_relat_1 @ X5 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X5 ) ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('243',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('244',plain,(
    ! [X33: $i] :
      ( ( v1_funct_2 @ X33 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('245',plain,(
    ! [X33: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X33 ) @ ( k2_relat_1 @ X33 ) ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(d4_tops_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( k2_tops_2 @ A @ B @ C )
          = ( k2_funct_1 @ C ) ) ) ) )).

thf('246',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X36 @ X38 )
       != X36 )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_tops_2 @ X37 @ X36 @ X38 )
        = ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['244','248'])).

thf('250',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['249'])).

thf('251',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['243','250'])).

thf('252',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['242','252'])).

thf('254',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['241','253'])).

thf('255',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['240','255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['239','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( ( ( k2_tops_2 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k2_funct_1 @ X0 ) )
        = ( k2_funct_1 @ ( k2_funct_1 @ X0 ) ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,
    ( ( ( k2_tops_2 @ ( k2_relat_1 @ sk_C ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['238','259'])).

thf('261',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('262',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['78','79'])).

thf('263',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('266',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['260','261','262','263','264','265'])).

thf('267',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) )
      = ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['266'])).

thf('268',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('269',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('270',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['269','270'])).

thf('272',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['271','272'])).

thf('274',plain,
    ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C )
    | ~ ( l1_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['268','273'])).

thf('275',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['274','275'])).

thf('277',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('278',plain,
    ( ( k1_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('279',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('280',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('281',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('282',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['276','279','280','281'])).

thf('283',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['165','166'])).

thf('284',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X36 @ X38 )
       != X36 )
      | ~ ( v2_funct_1 @ X38 )
      | ( ( k2_tops_2 @ X37 @ X36 @ X38 )
        = ( k2_funct_1 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X36 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_2])).

thf('285',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) )
    | ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['283','284'])).

thf('286',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('288',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('289',plain,
    ( ( k2_relset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('290',plain,
    ( ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
      = ( k2_funct_1 @ sk_C ) )
    | ( ( k2_struct_0 @ sk_B )
     != ( k2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['285','286','287','288','289'])).

thf('291',plain,
    ( ( k2_tops_2 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_B ) @ sk_C )
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['290'])).

thf('292',plain,(
    ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tops_2 @ ( k2_struct_0 @ sk_B ) @ ( k2_struct_0 @ sk_A ) @ ( k2_funct_1 @ sk_C ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['282','291'])).

thf('293',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( k2_funct_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_C )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['267','292'])).

thf('294',plain,
    ( ~ ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','293'])).

thf('295',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('296',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('297',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_funct_2 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('298',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['296','297'])).

thf('299',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('300',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['298','299','300'])).

thf('302',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('303',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('304',plain,
    ( ( k2_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['277','278'])).

thf('305',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['301','302','303','304'])).

thf('306',plain,
    ( ( r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['295','305'])).

thf('307',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('308',plain,(
    v1_funct_2 @ sk_C @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['174','175'])).

thf('309',plain,(
    r2_funct_2 @ ( k2_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ sk_C ),
    inference(demod,[status(thm)],['306','307','308'])).

thf('310',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['78','79'])).

thf('311',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('312',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('313',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k2_struct_0 @ sk_B ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('314',plain,
    ( ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 )
    | ( ( k2_struct_0 @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['294','309','310','311','312','313'])).

thf('315',plain,
    ( ( k2_struct_0 @ sk_B )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['314'])).

thf('316',plain,(
    ! [X34: $i] :
      ( ( ( k2_struct_0 @ X34 )
        = ( u1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('317',plain,(
    ! [X35: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l1_struct_0 @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('318',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['316','317'])).

thf('319',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['318'])).

thf('320',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['315','319'])).

thf('321',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('322',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('323',plain,(
    v2_struct_0 @ sk_B ),
    inference(demod,[status(thm)],['320','321','322'])).

thf('324',plain,(
    $false ),
    inference(demod,[status(thm)],['0','323'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9DpKy2adAI
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:36:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.83/1.04  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.83/1.04  % Solved by: fo/fo7.sh
% 0.83/1.04  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.83/1.04  % done 1236 iterations in 0.588s
% 0.83/1.04  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.83/1.04  % SZS output start Refutation
% 0.83/1.04  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.83/1.04  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.83/1.04  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.83/1.04  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.83/1.04  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.83/1.04  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.83/1.04  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.83/1.04  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.83/1.04  thf(k2_tops_2_type, type, k2_tops_2: $i > $i > $i > $i).
% 0.83/1.04  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.83/1.04  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.83/1.04  thf(sk_C_type, type, sk_C: $i).
% 0.83/1.04  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.83/1.04  thf(sk_B_type, type, sk_B: $i).
% 0.83/1.04  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.83/1.04  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.83/1.04  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.83/1.04  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.83/1.04  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.83/1.04  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.83/1.04  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.83/1.04  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.83/1.04  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.83/1.04  thf(sk_A_type, type, sk_A: $i).
% 0.83/1.04  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.83/1.04  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.83/1.04  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.83/1.04  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.83/1.04  thf(t64_tops_2, conjecture,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( l1_struct_0 @ A ) =>
% 0.83/1.04       ( ![B:$i]:
% 0.83/1.04         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.83/1.04           ( ![C:$i]:
% 0.83/1.04             ( ( ( v1_funct_1 @ C ) & 
% 0.83/1.04                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/1.04                 ( m1_subset_1 @
% 0.83/1.04                   C @ 
% 0.83/1.04                   ( k1_zfmisc_1 @
% 0.83/1.04                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/1.04               ( ( ( ( k2_relset_1 @
% 0.83/1.04                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.83/1.04                     ( k2_struct_0 @ B ) ) & 
% 0.83/1.04                   ( v2_funct_1 @ C ) ) =>
% 0.83/1.04                 ( r2_funct_2 @
% 0.83/1.04                   ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.83/1.04                   ( k2_tops_2 @
% 0.83/1.04                     ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/1.04                     ( k2_tops_2 @
% 0.83/1.04                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.83/1.04                   C ) ) ) ) ) ) ))).
% 0.83/1.04  thf(zf_stmt_0, negated_conjecture,
% 0.83/1.04    (~( ![A:$i]:
% 0.83/1.04        ( ( l1_struct_0 @ A ) =>
% 0.83/1.04          ( ![B:$i]:
% 0.83/1.04            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.83/1.04              ( ![C:$i]:
% 0.83/1.04                ( ( ( v1_funct_1 @ C ) & 
% 0.83/1.04                    ( v1_funct_2 @
% 0.83/1.04                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.83/1.04                    ( m1_subset_1 @
% 0.83/1.04                      C @ 
% 0.83/1.04                      ( k1_zfmisc_1 @
% 0.83/1.04                        ( k2_zfmisc_1 @
% 0.83/1.04                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.83/1.04                  ( ( ( ( k2_relset_1 @
% 0.83/1.04                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) =
% 0.83/1.04                        ( k2_struct_0 @ B ) ) & 
% 0.83/1.04                      ( v2_funct_1 @ C ) ) =>
% 0.83/1.04                    ( r2_funct_2 @
% 0.83/1.04                      ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ 
% 0.83/1.04                      ( k2_tops_2 @
% 0.83/1.04                        ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ 
% 0.83/1.04                        ( k2_tops_2 @
% 0.83/1.04                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C ) ) @ 
% 0.83/1.04                      C ) ) ) ) ) ) ) )),
% 0.83/1.04    inference('cnf.neg', [status(esa)], [t64_tops_2])).
% 0.83/1.04  thf('0', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(t55_funct_1, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.83/1.04       ( ( v2_funct_1 @ A ) =>
% 0.83/1.04         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.83/1.04           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.83/1.04  thf('1', plain,
% 0.83/1.04      (![X5 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X5)
% 0.83/1.04          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.83/1.04          | ~ (v1_funct_1 @ X5)
% 0.83/1.04          | ~ (v1_relat_1 @ X5))),
% 0.83/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.83/1.04  thf(dt_k2_funct_1, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.83/1.04       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.83/1.04         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.83/1.04  thf('2', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('3', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('4', plain,
% 0.83/1.04      (![X5 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X5)
% 0.83/1.04          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.83/1.04          | ~ (v1_funct_1 @ X5)
% 0.83/1.04          | ~ (v1_relat_1 @ X5))),
% 0.83/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.83/1.04  thf('5', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('6', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf(t3_funct_2, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.83/1.04       ( ( v1_funct_1 @ A ) & 
% 0.83/1.04         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.83/1.04         ( m1_subset_1 @
% 0.83/1.04           A @ 
% 0.83/1.04           ( k1_zfmisc_1 @
% 0.83/1.04             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.83/1.04  thf('7', plain,
% 0.83/1.04      (![X33 : $i]:
% 0.83/1.04         ((m1_subset_1 @ X33 @ 
% 0.83/1.04           (k1_zfmisc_1 @ 
% 0.83/1.04            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 0.83/1.04          | ~ (v1_funct_1 @ X33)
% 0.83/1.04          | ~ (v1_relat_1 @ X33))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.83/1.04  thf(redefinition_k2_relset_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.04       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.83/1.04  thf('8', plain,
% 0.83/1.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.83/1.04         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.83/1.04          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.83/1.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.04  thf('9', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              = (k2_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['7', '8'])).
% 0.83/1.04  thf('10', plain,
% 0.83/1.04      (![X33 : $i]:
% 0.83/1.04         ((v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))
% 0.83/1.04          | ~ (v1_funct_1 @ X33)
% 0.83/1.04          | ~ (v1_relat_1 @ X33))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.83/1.04  thf('11', plain,
% 0.83/1.04      (![X33 : $i]:
% 0.83/1.04         ((m1_subset_1 @ X33 @ 
% 0.83/1.04           (k1_zfmisc_1 @ 
% 0.83/1.04            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 0.83/1.04          | ~ (v1_funct_1 @ X33)
% 0.83/1.04          | ~ (v1_relat_1 @ X33))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.83/1.04  thf(t35_funct_2, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.04       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.83/1.04         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.83/1.04           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.83/1.04             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.83/1.04  thf('12', plain,
% 0.83/1.04      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.83/1.04         (((X30) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_funct_1 @ X31)
% 0.83/1.04          | ~ (v1_funct_2 @ X31 @ X32 @ X30)
% 0.83/1.04          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 0.83/1.04          | ((k5_relat_1 @ X31 @ (k2_funct_1 @ X31)) = (k6_partfun1 @ X32))
% 0.83/1.04          | ~ (v2_funct_1 @ X31)
% 0.83/1.04          | ((k2_relset_1 @ X32 @ X30 @ X31) != (X30)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.83/1.04  thf('13', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              != (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.83/1.04              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.83/1.04          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['11', '12'])).
% 0.83/1.04  thf('14', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.83/1.04              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              != (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['13'])).
% 0.83/1.04  thf('15', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              != (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.83/1.04              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['10', '14'])).
% 0.83/1.04  thf('16', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.83/1.04              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              != (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['15'])).
% 0.83/1.04  thf('17', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.83/1.04              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['9', '16'])).
% 0.83/1.04  thf('18', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.83/1.04              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['17'])).
% 0.83/1.04  thf(t48_funct_1, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.83/1.04       ( ![B:$i]:
% 0.83/1.04         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.83/1.04           ( ( ( v2_funct_1 @ ( k5_relat_1 @ B @ A ) ) & 
% 0.83/1.04               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) ) =>
% 0.83/1.04             ( ( v2_funct_1 @ B ) & ( v2_funct_1 @ A ) ) ) ) ) ))).
% 0.83/1.04  thf('19', plain,
% 0.83/1.04      (![X3 : $i, X4 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X3)
% 0.83/1.04          | ~ (v1_funct_1 @ X3)
% 0.83/1.04          | (v2_funct_1 @ X4)
% 0.83/1.04          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.83/1.04          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 0.83/1.04          | ~ (v1_funct_1 @ X4)
% 0.83/1.04          | ~ (v1_relat_1 @ X4))),
% 0.83/1.04      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.83/1.04  thf('20', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['18', '19'])).
% 0.83/1.04  thf(fc4_funct_1, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.83/1.04       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.83/1.04  thf('21', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 0.83/1.04      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.83/1.04  thf(redefinition_k6_partfun1, axiom,
% 0.83/1.04    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.83/1.04  thf('22', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.83/1.04      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.83/1.04  thf('23', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 0.83/1.04      inference('demod', [status(thm)], ['21', '22'])).
% 0.83/1.04  thf('24', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('demod', [status(thm)], ['20', '23'])).
% 0.83/1.04  thf('25', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['24'])).
% 0.83/1.04  thf('26', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['6', '25'])).
% 0.83/1.04  thf('27', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['26'])).
% 0.83/1.04  thf('28', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['5', '27'])).
% 0.83/1.04  thf('29', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['28'])).
% 0.83/1.04  thf('30', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['4', '29'])).
% 0.83/1.04  thf('31', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['30'])).
% 0.83/1.04  thf('32', plain,
% 0.83/1.04      (![X5 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X5)
% 0.83/1.04          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.83/1.04          | ~ (v1_funct_1 @ X5)
% 0.83/1.04          | ~ (v1_relat_1 @ X5))),
% 0.83/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.83/1.04  thf('33', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ((k5_relat_1 @ X0 @ (k2_funct_1 @ X0))
% 0.83/1.04              = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['17'])).
% 0.83/1.04  thf(t64_funct_1, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.83/1.04       ( ![B:$i]:
% 0.83/1.04         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.83/1.04           ( ( ( v2_funct_1 @ A ) & 
% 0.83/1.04               ( ( k2_relat_1 @ B ) = ( k1_relat_1 @ A ) ) & 
% 0.83/1.04               ( ( k5_relat_1 @ B @ A ) = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) =>
% 0.83/1.04             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.83/1.04  thf('34', plain,
% 0.83/1.04      (![X6 : $i, X7 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X6)
% 0.83/1.04          | ~ (v1_funct_1 @ X6)
% 0.83/1.04          | ((X6) = (k2_funct_1 @ X7))
% 0.83/1.04          | ((k5_relat_1 @ X6 @ X7) != (k6_relat_1 @ (k2_relat_1 @ X7)))
% 0.83/1.04          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.83/1.04          | ~ (v2_funct_1 @ X7)
% 0.83/1.04          | ~ (v1_funct_1 @ X7)
% 0.83/1.04          | ~ (v1_relat_1 @ X7))),
% 0.83/1.04      inference('cnf', [status(esa)], [t64_funct_1])).
% 0.83/1.04  thf('35', plain, (![X19 : $i]: ((k6_partfun1 @ X19) = (k6_relat_1 @ X19))),
% 0.83/1.04      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.83/1.04  thf('36', plain,
% 0.83/1.04      (![X6 : $i, X7 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X6)
% 0.83/1.04          | ~ (v1_funct_1 @ X6)
% 0.83/1.04          | ((X6) = (k2_funct_1 @ X7))
% 0.83/1.04          | ((k5_relat_1 @ X6 @ X7) != (k6_partfun1 @ (k2_relat_1 @ X7)))
% 0.83/1.04          | ((k2_relat_1 @ X6) != (k1_relat_1 @ X7))
% 0.83/1.04          | ~ (v2_funct_1 @ X7)
% 0.83/1.04          | ~ (v1_funct_1 @ X7)
% 0.83/1.04          | ~ (v1_relat_1 @ X7))),
% 0.83/1.04      inference('demod', [status(thm)], ['34', '35'])).
% 0.83/1.04  thf('37', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.83/1.04            != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0))))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['33', '36'])).
% 0.83/1.04  thf('38', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.83/1.04              != (k6_partfun1 @ (k2_relat_1 @ (k2_funct_1 @ X0)))))),
% 0.83/1.04      inference('simplify', [status(thm)], ['37'])).
% 0.83/1.04  thf('39', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k6_partfun1 @ (k1_relat_1 @ X0))
% 0.83/1.04            != (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['32', '38'])).
% 0.83/1.04  thf('40', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['39'])).
% 0.83/1.04  thf('41', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['31', '40'])).
% 0.83/1.04  thf('42', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['41'])).
% 0.83/1.04  thf('43', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['3', '42'])).
% 0.83/1.04  thf('44', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['43'])).
% 0.83/1.04  thf('45', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['2', '44'])).
% 0.83/1.04  thf('46', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) != (k1_relat_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['45'])).
% 0.83/1.04  thf('47', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ((X0) = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['1', '46'])).
% 0.83/1.04  thf('48', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((X0) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['47'])).
% 0.83/1.04  thf('49', plain,
% 0.83/1.04      (![X5 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X5)
% 0.83/1.04          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.83/1.04          | ~ (v1_funct_1 @ X5)
% 0.83/1.04          | ~ (v1_relat_1 @ X5))),
% 0.83/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.83/1.04  thf('50', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('51', plain,
% 0.83/1.04      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.83/1.04         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.83/1.04          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.83/1.04      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.83/1.04  thf('52', plain,
% 0.83/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_relat_1 @ sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['50', '51'])).
% 0.83/1.04  thf('53', plain,
% 0.83/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('54', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['52', '53'])).
% 0.83/1.04  thf('55', plain,
% 0.83/1.04      (![X5 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X5)
% 0.83/1.04          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.83/1.04          | ~ (v1_funct_1 @ X5)
% 0.83/1.04          | ~ (v1_relat_1 @ X5))),
% 0.83/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.83/1.04  thf('56', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('57', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('58', plain,
% 0.83/1.04      (![X5 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X5)
% 0.83/1.04          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.83/1.04          | ~ (v1_funct_1 @ X5)
% 0.83/1.04          | ~ (v1_relat_1 @ X5))),
% 0.83/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.83/1.04  thf('59', plain,
% 0.83/1.04      (![X33 : $i]:
% 0.83/1.04         ((m1_subset_1 @ X33 @ 
% 0.83/1.04           (k1_zfmisc_1 @ 
% 0.83/1.04            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 0.83/1.04          | ~ (v1_funct_1 @ X33)
% 0.83/1.04          | ~ (v1_relat_1 @ X33))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.83/1.04  thf('60', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.83/1.04           (k1_zfmisc_1 @ 
% 0.83/1.04            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['58', '59'])).
% 0.83/1.04  thf('61', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.83/1.04             (k1_zfmisc_1 @ 
% 0.83/1.04              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.83/1.04               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['57', '60'])).
% 0.83/1.04  thf('62', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.83/1.04           (k1_zfmisc_1 @ 
% 0.83/1.04            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['61'])).
% 0.83/1.04  thf('63', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.83/1.04             (k1_zfmisc_1 @ 
% 0.83/1.04              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 0.83/1.04               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['56', '62'])).
% 0.83/1.04  thf('64', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.83/1.04           (k1_zfmisc_1 @ 
% 0.83/1.04            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['63'])).
% 0.83/1.04  thf('65', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.83/1.04           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0))),
% 0.83/1.04      inference('sup+', [status(thm)], ['55', '64'])).
% 0.83/1.04  thf('66', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 0.83/1.04             (k1_zfmisc_1 @ 
% 0.83/1.04              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))))),
% 0.83/1.04      inference('simplify', [status(thm)], ['65'])).
% 0.83/1.04  thf('67', plain,
% 0.83/1.04      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.83/1.04         (k1_zfmisc_1 @ 
% 0.83/1.04          (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k1_relat_1 @ sk_C))))
% 0.83/1.04        | ~ (v1_relat_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C))),
% 0.83/1.04      inference('sup+', [status(thm)], ['54', '66'])).
% 0.83/1.04  thf(d3_struct_0, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.83/1.04  thf('68', plain,
% 0.83/1.04      (![X34 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('69', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(t132_funct_2, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( ( v1_funct_1 @ C ) & 
% 0.83/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.04       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.04           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.04         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.83/1.04           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.83/1.04  thf('70', plain,
% 0.83/1.04      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.04         (((X24) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_funct_1 @ X25)
% 0.83/1.04          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 0.83/1.04          | (v1_partfun1 @ X25 @ X26)
% 0.83/1.04          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 0.83/1.04          | ~ (v1_funct_2 @ X25 @ X26 @ X24)
% 0.83/1.04          | ~ (v1_funct_1 @ X25))),
% 0.83/1.04      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.83/1.04  thf('71', plain,
% 0.83/1.04      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.83/1.04         (~ (v1_funct_2 @ X25 @ X26 @ X24)
% 0.83/1.04          | (v1_partfun1 @ X25 @ X26)
% 0.83/1.04          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X24)))
% 0.83/1.04          | ~ (v1_funct_1 @ X25)
% 0.83/1.04          | ((X24) = (k1_xboole_0)))),
% 0.83/1.04      inference('simplify', [status(thm)], ['70'])).
% 0.83/1.04  thf('72', plain,
% 0.83/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.83/1.04        | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['69', '71'])).
% 0.83/1.04  thf('73', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('74', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('75', plain,
% 0.83/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | (v1_partfun1 @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.83/1.04  thf(d4_partfun1, axiom,
% 0.83/1.04    (![A:$i,B:$i]:
% 0.83/1.04     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.83/1.04       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.83/1.04  thf('76', plain,
% 0.83/1.04      (![X17 : $i, X18 : $i]:
% 0.83/1.04         (~ (v1_partfun1 @ X18 @ X17)
% 0.83/1.04          | ((k1_relat_1 @ X18) = (X17))
% 0.83/1.04          | ~ (v4_relat_1 @ X18 @ X17)
% 0.83/1.04          | ~ (v1_relat_1 @ X18))),
% 0.83/1.04      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.83/1.04  thf('77', plain,
% 0.83/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ~ (v1_relat_1 @ sk_C)
% 0.83/1.04        | ~ (v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.83/1.04        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['75', '76'])).
% 0.83/1.04  thf('78', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(cc1_relset_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.04       ( v1_relat_1 @ C ) ))).
% 0.83/1.04  thf('79', plain,
% 0.83/1.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.83/1.04         ((v1_relat_1 @ X8)
% 0.83/1.04          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.83/1.04      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.83/1.04  thf('80', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['78', '79'])).
% 0.83/1.04  thf('81', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(cc2_relset_1, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.83/1.04       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.83/1.04  thf('82', plain,
% 0.83/1.04      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.83/1.04         ((v4_relat_1 @ X11 @ X12)
% 0.83/1.04          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.83/1.04      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.83/1.04  thf('83', plain, ((v4_relat_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('sup-', [status(thm)], ['81', '82'])).
% 0.83/1.04  thf('84', plain,
% 0.83/1.04      ((((u1_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.83/1.04      inference('demod', [status(thm)], ['77', '80', '83'])).
% 0.83/1.04  thf(fc2_struct_0, axiom,
% 0.83/1.04    (![A:$i]:
% 0.83/1.04     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.83/1.04       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.83/1.04  thf('85', plain,
% 0.83/1.04      (![X35 : $i]:
% 0.83/1.04         (~ (v1_xboole_0 @ (u1_struct_0 @ X35))
% 0.83/1.04          | ~ (l1_struct_0 @ X35)
% 0.83/1.04          | (v2_struct_0 @ X35))),
% 0.83/1.04      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.83/1.04  thf('86', plain,
% 0.83/1.04      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.04        | ((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))
% 0.83/1.04        | (v2_struct_0 @ sk_B)
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup-', [status(thm)], ['84', '85'])).
% 0.83/1.04  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.83/1.04  thf('87', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.04  thf('88', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('89', plain,
% 0.83/1.04      ((((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.83/1.04  thf('90', plain, (~ (v2_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('91', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('clc', [status(thm)], ['89', '90'])).
% 0.83/1.04  thf('92', plain,
% 0.83/1.04      ((((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.04      inference('sup+', [status(thm)], ['68', '91'])).
% 0.83/1.04  thf('93', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('94', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['92', '93'])).
% 0.83/1.04  thf('95', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['78', '79'])).
% 0.83/1.04  thf('96', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('97', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('98', plain,
% 0.83/1.04      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A))))),
% 0.83/1.04      inference('demod', [status(thm)], ['67', '94', '95', '96', '97'])).
% 0.83/1.04  thf('99', plain,
% 0.83/1.04      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.83/1.04         ((v1_relat_1 @ X8)
% 0.83/1.04          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.83/1.04      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.83/1.04  thf('100', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['98', '99'])).
% 0.83/1.04  thf('101', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('102', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['30'])).
% 0.83/1.04  thf('103', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('104', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('105', plain,
% 0.83/1.04      (![X5 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X5)
% 0.83/1.04          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.83/1.04          | ~ (v1_funct_1 @ X5)
% 0.83/1.04          | ~ (v1_relat_1 @ X5))),
% 0.83/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.83/1.04  thf('106', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('107', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('108', plain,
% 0.83/1.04      (![X5 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X5)
% 0.83/1.04          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.83/1.04          | ~ (v1_funct_1 @ X5)
% 0.83/1.04          | ~ (v1_relat_1 @ X5))),
% 0.83/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.83/1.04  thf('109', plain,
% 0.83/1.04      (![X33 : $i]:
% 0.83/1.04         ((m1_subset_1 @ X33 @ 
% 0.83/1.04           (k1_zfmisc_1 @ 
% 0.83/1.04            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 0.83/1.04          | ~ (v1_funct_1 @ X33)
% 0.83/1.04          | ~ (v1_relat_1 @ X33))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.83/1.04  thf('110', plain,
% 0.83/1.04      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.83/1.04         ((v4_relat_1 @ X11 @ X12)
% 0.83/1.04          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.83/1.04      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.83/1.04  thf('111', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['109', '110'])).
% 0.83/1.04  thf('112', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['108', '111'])).
% 0.83/1.04  thf('113', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['107', '112'])).
% 0.83/1.04  thf('114', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['113'])).
% 0.83/1.04  thf('115', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['106', '114'])).
% 0.83/1.04  thf('116', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['115'])).
% 0.83/1.04  thf('117', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['105', '116'])).
% 0.83/1.04  thf('118', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['104', '117'])).
% 0.83/1.04  thf('119', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['118'])).
% 0.83/1.04  thf('120', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['103', '119'])).
% 0.83/1.04  thf('121', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['120'])).
% 0.83/1.04  thf('122', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['102', '121'])).
% 0.83/1.04  thf('123', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['122'])).
% 0.83/1.04  thf('124', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['30'])).
% 0.83/1.04  thf('125', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('126', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('127', plain,
% 0.83/1.04      (![X5 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X5)
% 0.83/1.04          | ((k1_relat_1 @ X5) = (k2_relat_1 @ (k2_funct_1 @ X5)))
% 0.83/1.04          | ~ (v1_funct_1 @ X5)
% 0.83/1.04          | ~ (v1_relat_1 @ X5))),
% 0.83/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.83/1.04  thf('128', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('129', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('130', plain,
% 0.83/1.04      (![X5 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X5)
% 0.83/1.04          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.83/1.04          | ~ (v1_funct_1 @ X5)
% 0.83/1.04          | ~ (v1_relat_1 @ X5))),
% 0.83/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.83/1.04  thf('131', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['109', '110'])).
% 0.83/1.04  thf('132', plain,
% 0.83/1.04      (![X17 : $i, X18 : $i]:
% 0.83/1.04         (((k1_relat_1 @ X18) != (X17))
% 0.83/1.04          | (v1_partfun1 @ X18 @ X17)
% 0.83/1.04          | ~ (v4_relat_1 @ X18 @ X17)
% 0.83/1.04          | ~ (v1_relat_1 @ X18))),
% 0.83/1.04      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.83/1.04  thf('133', plain,
% 0.83/1.04      (![X18 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X18)
% 0.83/1.04          | ~ (v4_relat_1 @ X18 @ (k1_relat_1 @ X18))
% 0.83/1.04          | (v1_partfun1 @ X18 @ (k1_relat_1 @ X18)))),
% 0.83/1.04      inference('simplify', [status(thm)], ['132'])).
% 0.83/1.04  thf('134', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['131', '133'])).
% 0.83/1.04  thf('135', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['134'])).
% 0.83/1.04  thf('136', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['130', '135'])).
% 0.83/1.04  thf('137', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['129', '136'])).
% 0.83/1.04  thf('138', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['137'])).
% 0.83/1.04  thf('139', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | (v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['128', '138'])).
% 0.83/1.04  thf('140', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['139'])).
% 0.83/1.04  thf('141', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['127', '140'])).
% 0.83/1.04  thf('142', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['126', '141'])).
% 0.83/1.04  thf('143', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['142'])).
% 0.83/1.04  thf('144', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['125', '143'])).
% 0.83/1.04  thf('145', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['144'])).
% 0.83/1.04  thf('146', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | (v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['124', '145'])).
% 0.83/1.04  thf('147', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_partfun1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['146'])).
% 0.83/1.04  thf('148', plain,
% 0.83/1.04      (![X17 : $i, X18 : $i]:
% 0.83/1.04         (~ (v1_partfun1 @ X18 @ X17)
% 0.83/1.04          | ((k1_relat_1 @ X18) = (X17))
% 0.83/1.04          | ~ (v4_relat_1 @ X18 @ X17)
% 0.83/1.04          | ~ (v1_relat_1 @ X18))),
% 0.83/1.04      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.83/1.04  thf('149', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ~ (v4_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)) @ 
% 0.83/1.04               (k1_relat_1 @ X0))
% 0.83/1.04          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04              = (k1_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['147', '148'])).
% 0.83/1.04  thf('150', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04              = (k1_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['123', '149'])).
% 0.83/1.04  thf('151', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04              = (k1_relat_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['150'])).
% 0.83/1.04  thf('152', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04              = (k1_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['101', '151'])).
% 0.83/1.04  thf('153', plain,
% 0.83/1.04      ((((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.04          = (k1_relat_1 @ sk_C))
% 0.83/1.04        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v1_relat_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['100', '152'])).
% 0.83/1.04  thf('154', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['92', '93'])).
% 0.83/1.04  thf('155', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['52', '53'])).
% 0.83/1.04  thf('156', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('157', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['78', '79'])).
% 0.83/1.04  thf('159', plain,
% 0.83/1.04      (![X34 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('160', plain,
% 0.83/1.04      (![X34 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('161', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('162', plain,
% 0.83/1.04      (((m1_subset_1 @ sk_C @ 
% 0.83/1.04         (k1_zfmisc_1 @ 
% 0.83/1.04          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.04      inference('sup+', [status(thm)], ['160', '161'])).
% 0.83/1.04  thf('163', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('164', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('demod', [status(thm)], ['162', '163'])).
% 0.83/1.04  thf('165', plain,
% 0.83/1.04      (((m1_subset_1 @ sk_C @ 
% 0.83/1.04         (k1_zfmisc_1 @ 
% 0.83/1.04          (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['159', '164'])).
% 0.83/1.04  thf('166', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('167', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('demod', [status(thm)], ['165', '166'])).
% 0.83/1.04  thf(t31_funct_2, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.04       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.83/1.04         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.83/1.04           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.83/1.04           ( m1_subset_1 @
% 0.83/1.04             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.83/1.04  thf('168', plain,
% 0.83/1.04      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X27)
% 0.83/1.04          | ((k2_relset_1 @ X29 @ X28 @ X27) != (X28))
% 0.83/1.04          | (v1_funct_1 @ (k2_funct_1 @ X27))
% 0.83/1.04          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.83/1.04          | ~ (v1_funct_2 @ X27 @ X29 @ X28)
% 0.83/1.04          | ~ (v1_funct_1 @ X27))),
% 0.83/1.04      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.83/1.04  thf('169', plain,
% 0.83/1.04      ((~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.83/1.04        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04            != (k2_struct_0 @ sk_B))
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['167', '168'])).
% 0.83/1.04  thf('170', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('171', plain,
% 0.83/1.04      (![X34 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('172', plain,
% 0.83/1.04      (![X34 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('173', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('174', plain,
% 0.83/1.04      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.04      inference('sup+', [status(thm)], ['172', '173'])).
% 0.83/1.04  thf('175', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('176', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['174', '175'])).
% 0.83/1.04  thf('177', plain,
% 0.83/1.04      (((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['171', '176'])).
% 0.83/1.04  thf('178', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('179', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['177', '178'])).
% 0.83/1.04  thf('180', plain,
% 0.83/1.04      (![X34 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('181', plain,
% 0.83/1.04      (![X34 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('182', plain,
% 0.83/1.04      (((k2_relset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('183', plain,
% 0.83/1.04      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04          = (k2_struct_0 @ sk_B))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_A))),
% 0.83/1.04      inference('sup+', [status(thm)], ['181', '182'])).
% 0.83/1.04  thf('184', plain, ((l1_struct_0 @ sk_A)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('185', plain,
% 0.83/1.04      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['183', '184'])).
% 0.83/1.04  thf('186', plain,
% 0.83/1.04      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04          = (k2_struct_0 @ sk_B))
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['180', '185'])).
% 0.83/1.04  thf('187', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('188', plain,
% 0.83/1.04      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['186', '187'])).
% 0.83/1.04  thf('189', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('190', plain,
% 0.83/1.04      (((v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.83/1.04      inference('demod', [status(thm)], ['169', '170', '179', '188', '189'])).
% 0.83/1.04  thf('191', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.83/1.04      inference('simplify', [status(thm)], ['190'])).
% 0.83/1.04  thf('192', plain,
% 0.83/1.04      ((((k1_relat_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.04          = (k2_struct_0 @ sk_A))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('demod', [status(thm)],
% 0.83/1.04                ['153', '154', '155', '156', '157', '158', '191'])).
% 0.83/1.04  thf('193', plain,
% 0.83/1.04      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.83/1.04        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['49', '192'])).
% 0.83/1.04  thf('194', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['98', '99'])).
% 0.83/1.04  thf('195', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.83/1.04      inference('simplify', [status(thm)], ['190'])).
% 0.83/1.04  thf('196', plain,
% 0.83/1.04      ((((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A))
% 0.83/1.04        | ~ (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('demod', [status(thm)], ['193', '194', '195'])).
% 0.83/1.04  thf('197', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('demod', [status(thm)], ['165', '166'])).
% 0.83/1.04  thf('198', plain,
% 0.83/1.04      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.83/1.04         (((X30) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_funct_1 @ X31)
% 0.83/1.04          | ~ (v1_funct_2 @ X31 @ X32 @ X30)
% 0.83/1.04          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X30)))
% 0.83/1.04          | ((k5_relat_1 @ X31 @ (k2_funct_1 @ X31)) = (k6_partfun1 @ X32))
% 0.83/1.04          | ~ (v2_funct_1 @ X31)
% 0.83/1.04          | ((k2_relset_1 @ X32 @ X30 @ X31) != (X30)))),
% 0.83/1.04      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.83/1.04  thf('199', plain,
% 0.83/1.04      ((((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04          != (k2_struct_0 @ sk_B))
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C)
% 0.83/1.04        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.83/1.04            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 0.83/1.04        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.83/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['197', '198'])).
% 0.83/1.04  thf('200', plain,
% 0.83/1.04      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['186', '187'])).
% 0.83/1.04  thf('201', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('202', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['177', '178'])).
% 0.83/1.04  thf('203', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('204', plain,
% 0.83/1.04      ((((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.83/1.04        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.83/1.04            = (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('demod', [status(thm)], ['199', '200', '201', '202', '203'])).
% 0.83/1.04  thf('205', plain,
% 0.83/1.04      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))
% 0.83/1.04            = (k6_partfun1 @ (k2_struct_0 @ sk_A))))),
% 0.83/1.04      inference('simplify', [status(thm)], ['204'])).
% 0.83/1.04  thf('206', plain,
% 0.83/1.04      (![X3 : $i, X4 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X3)
% 0.83/1.04          | ~ (v1_funct_1 @ X3)
% 0.83/1.04          | (v2_funct_1 @ X4)
% 0.83/1.04          | ((k2_relat_1 @ X3) != (k1_relat_1 @ X4))
% 0.83/1.04          | ~ (v2_funct_1 @ (k5_relat_1 @ X3 @ X4))
% 0.83/1.04          | ~ (v1_funct_1 @ X4)
% 0.83/1.04          | ~ (v1_relat_1 @ X4))),
% 0.83/1.04      inference('cnf', [status(esa)], [t48_funct_1])).
% 0.83/1.04  thf('207', plain,
% 0.83/1.04      ((~ (v2_funct_1 @ (k6_partfun1 @ (k2_struct_0 @ sk_A)))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.04        | (v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v1_relat_1 @ sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['205', '206'])).
% 0.83/1.04  thf('208', plain, (![X2 : $i]: (v2_funct_1 @ (k6_partfun1 @ X2))),
% 0.83/1.04      inference('demod', [status(thm)], ['21', '22'])).
% 0.83/1.04  thf('209', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['98', '99'])).
% 0.83/1.04  thf('210', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.83/1.04      inference('simplify', [status(thm)], ['190'])).
% 0.83/1.04  thf('211', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['52', '53'])).
% 0.83/1.04  thf('212', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('213', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['52', '53'])).
% 0.83/1.04  thf('214', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_partfun1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['139'])).
% 0.83/1.04  thf('215', plain,
% 0.83/1.04      (((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.83/1.04        | ~ (v1_relat_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C))),
% 0.83/1.04      inference('sup+', [status(thm)], ['213', '214'])).
% 0.83/1.04  thf('216', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['78', '79'])).
% 0.83/1.04  thf('217', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('218', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('219', plain,
% 0.83/1.04      ((v1_partfun1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['215', '216', '217', '218'])).
% 0.83/1.04  thf('220', plain,
% 0.83/1.04      (![X17 : $i, X18 : $i]:
% 0.83/1.04         (~ (v1_partfun1 @ X18 @ X17)
% 0.83/1.04          | ((k1_relat_1 @ X18) = (X17))
% 0.83/1.04          | ~ (v4_relat_1 @ X18 @ X17)
% 0.83/1.04          | ~ (v1_relat_1 @ X18))),
% 0.83/1.04      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.83/1.04  thf('221', plain,
% 0.83/1.04      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ~ (v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.83/1.04        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['219', '220'])).
% 0.83/1.04  thf('222', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['52', '53'])).
% 0.83/1.04  thf('223', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['115'])).
% 0.83/1.04  thf('224', plain,
% 0.83/1.04      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))
% 0.83/1.04        | ~ (v1_relat_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C))),
% 0.83/1.04      inference('sup+', [status(thm)], ['222', '223'])).
% 0.83/1.04  thf('225', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['78', '79'])).
% 0.83/1.04  thf('226', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('227', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('228', plain,
% 0.83/1.04      ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['224', '225', '226', '227'])).
% 0.83/1.04  thf('229', plain,
% 0.83/1.04      ((~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.83/1.04      inference('demod', [status(thm)], ['221', '228'])).
% 0.83/1.04  thf('230', plain,
% 0.83/1.04      ((~ (v1_relat_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['212', '229'])).
% 0.83/1.04  thf('231', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['78', '79'])).
% 0.83/1.04  thf('232', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('233', plain,
% 0.83/1.04      (((k1_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['230', '231', '232'])).
% 0.83/1.04  thf('234', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('235', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['78', '79'])).
% 0.83/1.04  thf('236', plain,
% 0.83/1.04      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B))
% 0.83/1.04        | (v2_funct_1 @ (k2_funct_1 @ sk_C)))),
% 0.83/1.04      inference('demod', [status(thm)],
% 0.83/1.04                ['207', '208', '209', '210', '211', '233', '234', '235'])).
% 0.83/1.04  thf('237', plain,
% 0.83/1.04      (((v2_funct_1 @ (k2_funct_1 @ sk_C))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('simplify', [status(thm)], ['236'])).
% 0.83/1.04  thf('238', plain,
% 0.83/1.04      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ((k2_relat_1 @ (k2_funct_1 @ sk_C)) = (k2_struct_0 @ sk_A)))),
% 0.83/1.04      inference('clc', [status(thm)], ['196', '237'])).
% 0.83/1.04  thf('239', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['30'])).
% 0.83/1.04  thf('240', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('241', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.83/1.04  thf('242', plain,
% 0.83/1.04      (![X5 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X5)
% 0.83/1.04          | ((k2_relat_1 @ X5) = (k1_relat_1 @ (k2_funct_1 @ X5)))
% 0.83/1.04          | ~ (v1_funct_1 @ X5)
% 0.83/1.04          | ~ (v1_relat_1 @ X5))),
% 0.83/1.04      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.83/1.04  thf('243', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              = (k2_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['7', '8'])).
% 0.83/1.04  thf('244', plain,
% 0.83/1.04      (![X33 : $i]:
% 0.83/1.04         ((v1_funct_2 @ X33 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))
% 0.83/1.04          | ~ (v1_funct_1 @ X33)
% 0.83/1.04          | ~ (v1_relat_1 @ X33))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.83/1.04  thf('245', plain,
% 0.83/1.04      (![X33 : $i]:
% 0.83/1.04         ((m1_subset_1 @ X33 @ 
% 0.83/1.04           (k1_zfmisc_1 @ 
% 0.83/1.04            (k2_zfmisc_1 @ (k1_relat_1 @ X33) @ (k2_relat_1 @ X33))))
% 0.83/1.04          | ~ (v1_funct_1 @ X33)
% 0.83/1.04          | ~ (v1_relat_1 @ X33))),
% 0.83/1.04      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.83/1.04  thf(d4_tops_2, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i]:
% 0.83/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.04       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.83/1.04         ( ( k2_tops_2 @ A @ B @ C ) = ( k2_funct_1 @ C ) ) ) ))).
% 0.83/1.04  thf('246', plain,
% 0.83/1.04      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.83/1.04         (((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 0.83/1.04          | ~ (v2_funct_1 @ X38)
% 0.83/1.04          | ((k2_tops_2 @ X37 @ X36 @ X38) = (k2_funct_1 @ X38))
% 0.83/1.04          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.83/1.04          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.83/1.04          | ~ (v1_funct_1 @ X38))),
% 0.83/1.04      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.83/1.04  thf('247', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              = (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              != (k2_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['245', '246'])).
% 0.83/1.04  thf('248', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04            != (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              = (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['247'])).
% 0.83/1.04  thf('249', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              = (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              != (k2_relat_1 @ X0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['244', '248'])).
% 0.83/1.04  thf('250', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04            != (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              = (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['249'])).
% 0.83/1.04  thf('251', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_relat_1 @ X0) != (k2_relat_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              = (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['243', '250'])).
% 0.83/1.04  thf('252', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_tops_2 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.83/1.04              = (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['251'])).
% 0.83/1.04  thf('253', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_tops_2 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.83/1.04            (k2_funct_1 @ X0)) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['242', '252'])).
% 0.83/1.04  thf('254', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ((k2_tops_2 @ (k2_relat_1 @ X0) @ 
% 0.83/1.04              (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.83/1.04              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['241', '253'])).
% 0.83/1.04  thf('255', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_tops_2 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.83/1.04            (k2_funct_1 @ X0)) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['254'])).
% 0.83/1.04  thf('256', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_tops_2 @ (k2_relat_1 @ X0) @ 
% 0.83/1.04              (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.83/1.04              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['240', '255'])).
% 0.83/1.04  thf('257', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_tops_2 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.83/1.04            (k2_funct_1 @ X0)) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ (k2_funct_1 @ X0))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['256'])).
% 0.83/1.04  thf('258', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v1_relat_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ((k2_tops_2 @ (k2_relat_1 @ X0) @ 
% 0.83/1.04              (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k2_funct_1 @ X0))
% 0.83/1.04              = (k2_funct_1 @ (k2_funct_1 @ X0))))),
% 0.83/1.04      inference('sup-', [status(thm)], ['239', '257'])).
% 0.83/1.04  thf('259', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (((k2_tops_2 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ 
% 0.83/1.04            (k2_funct_1 @ X0)) = (k2_funct_1 @ (k2_funct_1 @ X0)))
% 0.83/1.04          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.83/1.04          | ~ (v2_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_relat_1 @ X0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['258'])).
% 0.83/1.04  thf('260', plain,
% 0.83/1.04      ((((k2_tops_2 @ (k2_relat_1 @ sk_C) @ (k2_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ~ (v1_relat_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C)
% 0.83/1.04        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 0.83/1.04      inference('sup+', [status(thm)], ['238', '259'])).
% 0.83/1.04  thf('261', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['52', '53'])).
% 0.83/1.04  thf('262', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['78', '79'])).
% 0.83/1.04  thf('263', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('264', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('265', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['52', '53'])).
% 0.83/1.04  thf('266', plain,
% 0.83/1.04      ((((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.83/1.04          (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C)))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('demod', [status(thm)],
% 0.83/1.04                ['260', '261', '262', '263', '264', '265'])).
% 0.83/1.04  thf('267', plain,
% 0.83/1.04      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ((k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.83/1.04            (k2_funct_1 @ sk_C)) = (k2_funct_1 @ (k2_funct_1 @ sk_C))))),
% 0.83/1.04      inference('simplify', [status(thm)], ['266'])).
% 0.83/1.04  thf('268', plain,
% 0.83/1.04      (![X34 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('269', plain,
% 0.83/1.04      (![X34 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('270', plain,
% 0.83/1.04      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.04          sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('271', plain,
% 0.83/1.04      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.04           sk_C)
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup-', [status(thm)], ['269', '270'])).
% 0.83/1.04  thf('272', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('273', plain,
% 0.83/1.04      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.04          (k2_tops_2 @ (u1_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.04          sk_C)),
% 0.83/1.04      inference('demod', [status(thm)], ['271', '272'])).
% 0.83/1.04  thf('274', plain,
% 0.83/1.04      ((~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.04           (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04            (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.04           sk_C)
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup-', [status(thm)], ['268', '273'])).
% 0.83/1.04  thf('275', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('276', plain,
% 0.83/1.04      (~ (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.04          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (u1_struct_0 @ sk_A) @ 
% 0.83/1.04           (k2_tops_2 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.04          sk_C)),
% 0.83/1.04      inference('demod', [status(thm)], ['274', '275'])).
% 0.83/1.04  thf('277', plain, (((k1_relat_1 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('clc', [status(thm)], ['89', '90'])).
% 0.83/1.04  thf('278', plain, (((k1_relat_1 @ sk_C) = (k2_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['92', '93'])).
% 0.83/1.04  thf('279', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['277', '278'])).
% 0.83/1.04  thf('280', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['277', '278'])).
% 0.83/1.04  thf('281', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['277', '278'])).
% 0.83/1.04  thf('282', plain,
% 0.83/1.04      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.04          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.83/1.04           (k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)) @ 
% 0.83/1.04          sk_C)),
% 0.83/1.04      inference('demod', [status(thm)], ['276', '279', '280', '281'])).
% 0.83/1.04  thf('283', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))))),
% 0.83/1.04      inference('demod', [status(thm)], ['165', '166'])).
% 0.83/1.04  thf('284', plain,
% 0.83/1.04      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.83/1.04         (((k2_relset_1 @ X37 @ X36 @ X38) != (X36))
% 0.83/1.04          | ~ (v2_funct_1 @ X38)
% 0.83/1.04          | ((k2_tops_2 @ X37 @ X36 @ X38) = (k2_funct_1 @ X38))
% 0.83/1.04          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36)))
% 0.83/1.04          | ~ (v1_funct_2 @ X38 @ X37 @ X36)
% 0.83/1.04          | ~ (v1_funct_1 @ X38))),
% 0.83/1.04      inference('cnf', [status(esa)], [d4_tops_2])).
% 0.83/1.04  thf('285', plain,
% 0.83/1.04      ((~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))
% 0.83/1.04        | ((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04            = (k2_funct_1 @ sk_C))
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C)
% 0.83/1.04        | ((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04            != (k2_struct_0 @ sk_B)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['283', '284'])).
% 0.83/1.04  thf('286', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('287', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['177', '178'])).
% 0.83/1.04  thf('288', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('289', plain,
% 0.83/1.04      (((k2_relset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['186', '187'])).
% 0.83/1.04  thf('290', plain,
% 0.83/1.04      ((((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04          = (k2_funct_1 @ sk_C))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) != (k2_struct_0 @ sk_B)))),
% 0.83/1.04      inference('demod', [status(thm)], ['285', '286', '287', '288', '289'])).
% 0.83/1.04  thf('291', plain,
% 0.83/1.04      (((k2_tops_2 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_B) @ sk_C)
% 0.83/1.04         = (k2_funct_1 @ sk_C))),
% 0.83/1.04      inference('simplify', [status(thm)], ['290'])).
% 0.83/1.04  thf('292', plain,
% 0.83/1.04      (~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.04          (k2_tops_2 @ (k2_struct_0 @ sk_B) @ (k2_struct_0 @ sk_A) @ 
% 0.83/1.04           (k2_funct_1 @ sk_C)) @ 
% 0.83/1.04          sk_C)),
% 0.83/1.04      inference('demod', [status(thm)], ['282', '291'])).
% 0.83/1.04  thf('293', plain,
% 0.83/1.04      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.83/1.04           (k2_funct_1 @ (k2_funct_1 @ sk_C)) @ sk_C)
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['267', '292'])).
% 0.83/1.04  thf('294', plain,
% 0.83/1.04      ((~ (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.04           sk_C)
% 0.83/1.04        | ~ (v1_relat_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v2_funct_1 @ sk_C)
% 0.83/1.04        | ((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['48', '293'])).
% 0.83/1.04  thf('295', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('demod', [status(thm)], ['162', '163'])).
% 0.83/1.04  thf('296', plain,
% 0.83/1.04      ((m1_subset_1 @ sk_C @ 
% 0.83/1.04        (k1_zfmisc_1 @ 
% 0.83/1.04         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf(reflexivity_r2_funct_2, axiom,
% 0.83/1.04    (![A:$i,B:$i,C:$i,D:$i]:
% 0.83/1.04     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.83/1.04         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.83/1.04         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.83/1.04         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.83/1.04       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.83/1.04  thf('297', plain,
% 0.83/1.04      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.83/1.04         ((r2_funct_2 @ X20 @ X21 @ X22 @ X22)
% 0.83/1.04          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.83/1.04          | ~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.83/1.04          | ~ (v1_funct_1 @ X22)
% 0.83/1.04          | ~ (v1_funct_1 @ X23)
% 0.83/1.04          | ~ (v1_funct_2 @ X23 @ X20 @ X21)
% 0.83/1.04          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.83/1.04      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.83/1.04  thf('298', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X0 @ 
% 0.83/1.04             (k1_zfmisc_1 @ 
% 0.83/1.04              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.83/1.04          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/1.04          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.04             sk_C))),
% 0.83/1.04      inference('sup-', [status(thm)], ['296', '297'])).
% 0.83/1.04  thf('299', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('300', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('301', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X0 @ 
% 0.83/1.04             (k1_zfmisc_1 @ 
% 0.83/1.04              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.83/1.04          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | (r2_funct_2 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.04             sk_C))),
% 0.83/1.04      inference('demod', [status(thm)], ['298', '299', '300'])).
% 0.83/1.04  thf('302', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['277', '278'])).
% 0.83/1.04  thf('303', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['277', '278'])).
% 0.83/1.04  thf('304', plain, (((k2_struct_0 @ sk_A) = (u1_struct_0 @ sk_A))),
% 0.83/1.04      inference('demod', [status(thm)], ['277', '278'])).
% 0.83/1.04  thf('305', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (m1_subset_1 @ X0 @ 
% 0.83/1.04             (k1_zfmisc_1 @ 
% 0.83/1.04              (k2_zfmisc_1 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))
% 0.83/1.04          | ~ (v1_funct_2 @ X0 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.83/1.04          | ~ (v1_funct_1 @ X0)
% 0.83/1.04          | (r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 0.83/1.04             sk_C))),
% 0.83/1.04      inference('demod', [status(thm)], ['301', '302', '303', '304'])).
% 0.83/1.04  thf('306', plain,
% 0.83/1.04      (((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)
% 0.83/1.04        | ~ (v1_funct_1 @ sk_C)
% 0.83/1.04        | ~ (v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B)))),
% 0.83/1.04      inference('sup-', [status(thm)], ['295', '305'])).
% 0.83/1.04  thf('307', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('308', plain,
% 0.83/1.04      ((v1_funct_2 @ sk_C @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.83/1.04      inference('demod', [status(thm)], ['174', '175'])).
% 0.83/1.04  thf('309', plain,
% 0.83/1.04      ((r2_funct_2 @ (k2_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ sk_C)),
% 0.83/1.04      inference('demod', [status(thm)], ['306', '307', '308'])).
% 0.83/1.04  thf('310', plain, ((v1_relat_1 @ sk_C)),
% 0.83/1.04      inference('sup-', [status(thm)], ['78', '79'])).
% 0.83/1.04  thf('311', plain, ((v1_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('312', plain, ((v2_funct_1 @ sk_C)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('313', plain, (((k2_relat_1 @ sk_C) = (k2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup+', [status(thm)], ['52', '53'])).
% 0.83/1.04  thf('314', plain,
% 0.83/1.04      ((((k2_struct_0 @ sk_B) = (k1_xboole_0))
% 0.83/1.04        | ((k2_struct_0 @ sk_B) = (k1_xboole_0)))),
% 0.83/1.04      inference('demod', [status(thm)],
% 0.83/1.04                ['294', '309', '310', '311', '312', '313'])).
% 0.83/1.04  thf('315', plain, (((k2_struct_0 @ sk_B) = (k1_xboole_0))),
% 0.83/1.04      inference('simplify', [status(thm)], ['314'])).
% 0.83/1.04  thf('316', plain,
% 0.83/1.04      (![X34 : $i]:
% 0.83/1.04         (((k2_struct_0 @ X34) = (u1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 0.83/1.04      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.83/1.04  thf('317', plain,
% 0.83/1.04      (![X35 : $i]:
% 0.83/1.04         (~ (v1_xboole_0 @ (u1_struct_0 @ X35))
% 0.83/1.04          | ~ (l1_struct_0 @ X35)
% 0.83/1.04          | (v2_struct_0 @ X35))),
% 0.83/1.04      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.83/1.04  thf('318', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.83/1.04          | ~ (l1_struct_0 @ X0)
% 0.83/1.04          | (v2_struct_0 @ X0)
% 0.83/1.04          | ~ (l1_struct_0 @ X0))),
% 0.83/1.04      inference('sup-', [status(thm)], ['316', '317'])).
% 0.83/1.04  thf('319', plain,
% 0.83/1.04      (![X0 : $i]:
% 0.83/1.04         ((v2_struct_0 @ X0)
% 0.83/1.04          | ~ (l1_struct_0 @ X0)
% 0.83/1.04          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.83/1.04      inference('simplify', [status(thm)], ['318'])).
% 0.83/1.04  thf('320', plain,
% 0.83/1.04      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.83/1.04        | ~ (l1_struct_0 @ sk_B)
% 0.83/1.04        | (v2_struct_0 @ sk_B))),
% 0.83/1.04      inference('sup-', [status(thm)], ['315', '319'])).
% 0.83/1.04  thf('321', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.83/1.04      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.83/1.04  thf('322', plain, ((l1_struct_0 @ sk_B)),
% 0.83/1.04      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.83/1.04  thf('323', plain, ((v2_struct_0 @ sk_B)),
% 0.83/1.04      inference('demod', [status(thm)], ['320', '321', '322'])).
% 0.83/1.04  thf('324', plain, ($false), inference('demod', [status(thm)], ['0', '323'])).
% 0.83/1.04  
% 0.83/1.04  % SZS output end Refutation
% 0.83/1.04  
% 0.83/1.05  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
