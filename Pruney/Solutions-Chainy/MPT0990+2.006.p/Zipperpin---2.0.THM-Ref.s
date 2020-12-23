%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2oHB3NzfyY

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:54 EST 2020

% Result     : Theorem 8.10s
% Output     : Refutation 8.10s
% Verified   : 
% Statistics : Number of formulae       :  319 (1489 expanded)
%              Number of leaves         :   46 ( 480 expanded)
%              Depth                    :   26
%              Number of atoms          : 2803 (24906 expanded)
%              Number of equality atoms :  144 (1668 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X22 ) @ X22 )
        = ( k6_relat_1 @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X22 ) @ X22 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X22: $i] :
      ( ~ ( v2_funct_1 @ X22 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X22 ) @ X22 )
        = ( k6_partfun1 @ ( k2_relat_1 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('5',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k2_relset_1 @ X30 @ X31 @ X29 )
        = ( k2_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k2_relat_1 @ X21 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('14',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ( v4_relat_1 @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ( v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['20','23','24','25'])).

thf(fc26_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A )
        & ( v1_relat_1 @ C ) )
     => ( ( v1_relat_1 @ ( k5_relat_1 @ B @ C ) )
        & ( v4_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X16 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc26_relat_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 )
        = ( k7_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k7_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['8','9'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('37',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('38',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('39',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('41',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('44',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k7_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['35','36','39','40','41','42','43'])).

thf('45',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
      = ( k7_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_C ) ) @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['3','44'])).

thf('46',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('47',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('48',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('49',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ( ( k6_partfun1 @ X0 )
        = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k6_partfun1 @ X0 )
      = ( k7_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('57',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','55','56','57','58'])).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('60',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf('61',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('62',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(t55_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C )
                = ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) )).

thf('64',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('71',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc26_relat_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('76',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','76'])).

thf('78',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('79',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ( ( k5_relat_1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_D @ X0 )
        = ( k5_relat_1 @ sk_D @ ( k5_relat_1 @ X0 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
      = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['68','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('89',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('90',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('91',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('93',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X16 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc26_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ ( k5_relat_1 @ sk_D @ X0 ) @ sk_B )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( ( v4_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) @ sk_B )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['91','96'])).

thf('98',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('99',plain,(
    v4_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) @ sk_B ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('101',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
      = ( k7_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('104',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc26_relat_1])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['102','106'])).

thf('108',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('109',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('110',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = ( k7_relat_1 @ ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['101','110'])).

thf('112',plain,
    ( ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
      = ( k7_relat_1 @ sk_D @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['62','111'])).

thf('113',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['69','70'])).

thf('114',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v4_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('115',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('117',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('119',plain,
    ( ( k5_relat_1 @ sk_D @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) )
    = sk_D ),
    inference(demod,[status(thm)],['112','117','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_partfun1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('121',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fc26_relat_1])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['124','128'])).

thf('130',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X1 ) @ ( k5_relat_1 @ X0 @ X2 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ sk_D ) ) ) ) ),
    inference('sup+',[status(thm)],['119','132'])).

thf('134',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('135',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('136',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['133','134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('138',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k5_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ sk_D )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ sk_D ) ) ) ) ) ),
    inference('sup-',[status(thm)],['136','139'])).

thf('141',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ sk_D )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k5_relat_1 @ ( k6_partfun1 @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) @ sk_D ) ) ) ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('143',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('144',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('145',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('146',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('147',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('148',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('149',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
        = ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['149','150'])).

thf('152',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) )
      = ( k6_partfun1 @ X0 ) ) ),
    inference(demod,[status(thm)],['151','152'])).

thf('154',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X8 @ X7 ) @ X9 )
        = ( k5_relat_1 @ X8 @ ( k5_relat_1 @ X7 @ X9 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t55_relat_1])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['153','154'])).

thf('156',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('157',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['155','156','157'])).

thf('159',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['146','158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['145','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('165',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('166',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ X1 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('167',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['164','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ sk_D @ X0 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['163','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ sk_D )
        = ( k5_relat_1 @ X1 @ ( k5_relat_1 @ X0 @ ( k7_relat_1 @ sk_D @ ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ) ) ) ),
    inference(demod,[status(thm)],['142','172'])).

thf('174',plain,
    ( ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) )
    | ( ( k5_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) @ sk_D )
      = ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k5_relat_1 @ sk_C @ ( k7_relat_1 @ sk_D @ ( k2_relat_1 @ ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C ) ) ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','173'])).

thf('175',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('176',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','55','56','57','58'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ sk_D @ X0 )
      = ( k5_relat_1 @ ( k6_partfun1 @ X0 ) @ sk_D ) ) ),
    inference(demod,[status(thm)],['170','171'])).

thf('178',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('179',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ sk_C )
    = ( k6_partfun1 @ sk_B ) ),
    inference(demod,[status(thm)],['45','46','55','56','57','58'])).

thf('180',plain,(
    ! [X11: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X11 ) )
      = X11 ) ),
    inference(demod,[status(thm)],['147','148'])).

thf('181',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('182',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('185',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ( ( k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46 )
        = ( k5_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('186',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['183','188'])).

thf('190',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['182','191'])).

thf('193',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('195',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('196',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('198',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['193','198'])).

thf('200',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['199','200'])).

thf('202',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('203',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('204',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( X32 = X35 )
      | ~ ( r2_relset_1 @ X33 @ X34 @ X32 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('205',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['192','205'])).

thf('207',plain,(
    ! [X36: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('208',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('209',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('210',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_partfun1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(demod,[status(thm)],['143','144'])).

thf('211',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['8','9'])).

thf('212',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('213',plain,
    ( ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
      = sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['211','212'])).

thf('214',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('215',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_partfun1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X2 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('217',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k6_partfun1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('219',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('220',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( k6_partfun1 @ X19 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k5_relat_1 @ ( k6_partfun1 @ sk_B ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['217','218','219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k7_relat_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['210','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ ( k7_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['222'])).

thf('224',plain,
    ( ( v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['209','223'])).

thf('225',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('226',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['224','225'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('228',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X16 @ X18 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc26_relat_1])).

thf('229',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('232',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['230','231'])).

thf('233',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['226','232'])).

thf('234',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['74','75'])).

thf('235',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('236',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) @ ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['233','234','235'])).

thf('237',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('238',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) )
    | ( ( k1_relat_1 @ sk_C )
      = ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['236','237'])).

thf('239',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('240',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('241',plain,(
    ! [X49: $i] :
      ( ( k6_partfun1 @ X49 )
      = ( k6_relat_1 @ X49 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('242',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('243',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v4_relat_1 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('245',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['243','244'])).

thf('246',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v4_relat_1 @ X3 @ X4 )
      | ( r1_tarski @ ( k1_relat_1 @ X3 ) @ X4 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('247',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('249',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['206','207'])).

thf('251',plain,(
    ! [X10: $i] :
      ( ( k1_relat_1 @ ( k6_partfun1 @ X10 ) )
      = X10 ) ),
    inference(demod,[status(thm)],['240','241'])).

thf('252',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['238','239','242','249','250','251'])).

thf('253',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('254',plain,(
    ! [X21: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k1_relat_1 @ X21 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('255',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_partfun1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['254','255'])).

thf('257',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['253','256'])).

thf('258',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['257'])).

thf('259',plain,
    ( ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['252','258'])).

thf('260',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('261',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('262',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( k5_relat_1 @ ( k2_funct_1 @ sk_C ) @ ( k6_partfun1 @ sk_A ) )
    = ( k2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['259','260','261','262'])).

thf('264',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('265',plain,
    ( ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['174','175','176','177','178','179','180','181','208','263','264'])).

thf('266',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('simplify_reflect-',[status(thm)],['265','266'])).

thf('268',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','267'])).

thf('269',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('270',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    $false ),
    inference(demod,[status(thm)],['268','269','270'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2oHB3NzfyY
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:37:45 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 8.10/8.29  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.10/8.29  % Solved by: fo/fo7.sh
% 8.10/8.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.10/8.29  % done 8562 iterations in 7.826s
% 8.10/8.29  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.10/8.29  % SZS output start Refutation
% 8.10/8.29  thf(sk_A_type, type, sk_A: $i).
% 8.10/8.29  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 8.10/8.29  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 8.10/8.29  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 8.10/8.29  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 8.10/8.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.10/8.29  thf(sk_D_type, type, sk_D: $i).
% 8.10/8.29  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.10/8.29  thf(sk_C_type, type, sk_C: $i).
% 8.10/8.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.10/8.29  thf(sk_B_type, type, sk_B: $i).
% 8.10/8.29  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 8.10/8.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.10/8.29  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.10/8.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.10/8.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.10/8.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.10/8.29  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 8.10/8.29  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 8.10/8.29  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 8.10/8.29  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 8.10/8.29  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 8.10/8.29  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 8.10/8.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.10/8.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.10/8.29  thf(dt_k2_funct_1, axiom,
% 8.10/8.29    (![A:$i]:
% 8.10/8.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.10/8.29       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 8.10/8.29         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 8.10/8.29  thf('0', plain,
% 8.10/8.29      (![X15 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 8.10/8.29          | ~ (v1_funct_1 @ X15)
% 8.10/8.29          | ~ (v1_relat_1 @ X15))),
% 8.10/8.29      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.10/8.29  thf(t61_funct_1, axiom,
% 8.10/8.29    (![A:$i]:
% 8.10/8.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.10/8.29       ( ( v2_funct_1 @ A ) =>
% 8.10/8.29         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 8.10/8.29             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 8.10/8.29           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 8.10/8.29             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 8.10/8.29  thf('1', plain,
% 8.10/8.29      (![X22 : $i]:
% 8.10/8.29         (~ (v2_funct_1 @ X22)
% 8.10/8.29          | ((k5_relat_1 @ (k2_funct_1 @ X22) @ X22)
% 8.10/8.29              = (k6_relat_1 @ (k2_relat_1 @ X22)))
% 8.10/8.29          | ~ (v1_funct_1 @ X22)
% 8.10/8.29          | ~ (v1_relat_1 @ X22))),
% 8.10/8.29      inference('cnf', [status(esa)], [t61_funct_1])).
% 8.10/8.29  thf(redefinition_k6_partfun1, axiom,
% 8.10/8.29    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 8.10/8.29  thf('2', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 8.10/8.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.10/8.29  thf('3', plain,
% 8.10/8.29      (![X22 : $i]:
% 8.10/8.29         (~ (v2_funct_1 @ X22)
% 8.10/8.29          | ((k5_relat_1 @ (k2_funct_1 @ X22) @ X22)
% 8.10/8.29              = (k6_partfun1 @ (k2_relat_1 @ X22)))
% 8.10/8.29          | ~ (v1_funct_1 @ X22)
% 8.10/8.29          | ~ (v1_relat_1 @ X22))),
% 8.10/8.29      inference('demod', [status(thm)], ['1', '2'])).
% 8.10/8.29  thf('4', plain,
% 8.10/8.29      (![X22 : $i]:
% 8.10/8.29         (~ (v2_funct_1 @ X22)
% 8.10/8.29          | ((k5_relat_1 @ (k2_funct_1 @ X22) @ X22)
% 8.10/8.29              = (k6_partfun1 @ (k2_relat_1 @ X22)))
% 8.10/8.29          | ~ (v1_funct_1 @ X22)
% 8.10/8.29          | ~ (v1_relat_1 @ X22))),
% 8.10/8.29      inference('demod', [status(thm)], ['1', '2'])).
% 8.10/8.29  thf('5', plain,
% 8.10/8.29      (![X15 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 8.10/8.29          | ~ (v1_funct_1 @ X15)
% 8.10/8.29          | ~ (v1_relat_1 @ X15))),
% 8.10/8.29      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.10/8.29  thf(t36_funct_2, conjecture,
% 8.10/8.29    (![A:$i,B:$i,C:$i]:
% 8.10/8.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.10/8.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.10/8.29       ( ![D:$i]:
% 8.10/8.29         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.10/8.29             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.10/8.29           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 8.10/8.29               ( r2_relset_1 @
% 8.10/8.29                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 8.10/8.29                 ( k6_partfun1 @ A ) ) & 
% 8.10/8.29               ( v2_funct_1 @ C ) ) =>
% 8.10/8.29             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 8.10/8.29               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 8.10/8.29  thf(zf_stmt_0, negated_conjecture,
% 8.10/8.29    (~( ![A:$i,B:$i,C:$i]:
% 8.10/8.29        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.10/8.29            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.10/8.29          ( ![D:$i]:
% 8.10/8.29            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 8.10/8.29                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 8.10/8.29              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 8.10/8.29                  ( r2_relset_1 @
% 8.10/8.29                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 8.10/8.29                    ( k6_partfun1 @ A ) ) & 
% 8.10/8.29                  ( v2_funct_1 @ C ) ) =>
% 8.10/8.29                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 8.10/8.29                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 8.10/8.29    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 8.10/8.29  thf('6', plain,
% 8.10/8.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf(redefinition_k2_relset_1, axiom,
% 8.10/8.29    (![A:$i,B:$i,C:$i]:
% 8.10/8.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.10/8.29       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 8.10/8.29  thf('7', plain,
% 8.10/8.29      (![X29 : $i, X30 : $i, X31 : $i]:
% 8.10/8.29         (((k2_relset_1 @ X30 @ X31 @ X29) = (k2_relat_1 @ X29))
% 8.10/8.29          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 8.10/8.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 8.10/8.29  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 8.10/8.29      inference('sup-', [status(thm)], ['6', '7'])).
% 8.10/8.29  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('10', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.10/8.29      inference('sup+', [status(thm)], ['8', '9'])).
% 8.10/8.29  thf('11', plain,
% 8.10/8.29      (![X15 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 8.10/8.29          | ~ (v1_funct_1 @ X15)
% 8.10/8.29          | ~ (v1_relat_1 @ X15))),
% 8.10/8.29      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.10/8.29  thf(t55_funct_1, axiom,
% 8.10/8.29    (![A:$i]:
% 8.10/8.29     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.10/8.29       ( ( v2_funct_1 @ A ) =>
% 8.10/8.29         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 8.10/8.29           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 8.10/8.29  thf('12', plain,
% 8.10/8.29      (![X21 : $i]:
% 8.10/8.29         (~ (v2_funct_1 @ X21)
% 8.10/8.29          | ((k2_relat_1 @ X21) = (k1_relat_1 @ (k2_funct_1 @ X21)))
% 8.10/8.29          | ~ (v1_funct_1 @ X21)
% 8.10/8.29          | ~ (v1_relat_1 @ X21))),
% 8.10/8.29      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.10/8.29  thf(d10_xboole_0, axiom,
% 8.10/8.29    (![A:$i,B:$i]:
% 8.10/8.29     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.10/8.29  thf('13', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 8.10/8.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.10/8.29  thf('14', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.10/8.29      inference('simplify', [status(thm)], ['13'])).
% 8.10/8.29  thf(d18_relat_1, axiom,
% 8.10/8.29    (![A:$i,B:$i]:
% 8.10/8.29     ( ( v1_relat_1 @ B ) =>
% 8.10/8.29       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 8.10/8.29  thf('15', plain,
% 8.10/8.29      (![X3 : $i, X4 : $i]:
% 8.10/8.29         (~ (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 8.10/8.29          | (v4_relat_1 @ X3 @ X4)
% 8.10/8.29          | ~ (v1_relat_1 @ X3))),
% 8.10/8.29      inference('cnf', [status(esa)], [d18_relat_1])).
% 8.10/8.29  thf('16', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['14', '15'])).
% 8.10/8.29  thf('17', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_funct_1 @ X0)
% 8.10/8.29          | ~ (v2_funct_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 8.10/8.29      inference('sup+', [status(thm)], ['12', '16'])).
% 8.10/8.29  thf('18', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_funct_1 @ X0)
% 8.10/8.29          | ~ (v2_funct_1 @ X0)
% 8.10/8.29          | ~ (v1_funct_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | (v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['11', '17'])).
% 8.10/8.29  thf('19', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((v4_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 8.10/8.29          | ~ (v2_funct_1 @ X0)
% 8.10/8.29          | ~ (v1_funct_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('simplify', [status(thm)], ['18'])).
% 8.10/8.29  thf('20', plain,
% 8.10/8.29      (((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)
% 8.10/8.29        | ~ (v1_relat_1 @ sk_C)
% 8.10/8.29        | ~ (v1_funct_1 @ sk_C)
% 8.10/8.29        | ~ (v2_funct_1 @ sk_C))),
% 8.10/8.29      inference('sup+', [status(thm)], ['10', '19'])).
% 8.10/8.29  thf('21', plain,
% 8.10/8.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf(cc1_relset_1, axiom,
% 8.10/8.29    (![A:$i,B:$i,C:$i]:
% 8.10/8.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.10/8.29       ( v1_relat_1 @ C ) ))).
% 8.10/8.29  thf('22', plain,
% 8.10/8.29      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.10/8.29         ((v1_relat_1 @ X23)
% 8.10/8.29          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 8.10/8.29      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.10/8.29  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('25', plain, ((v2_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('26', plain, ((v4_relat_1 @ (k2_funct_1 @ sk_C) @ sk_B)),
% 8.10/8.29      inference('demod', [status(thm)], ['20', '23', '24', '25'])).
% 8.10/8.29  thf(fc26_relat_1, axiom,
% 8.10/8.29    (![A:$i,B:$i,C:$i]:
% 8.10/8.29     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) & ( v1_relat_1 @ C ) ) =>
% 8.10/8.29       ( ( v1_relat_1 @ ( k5_relat_1 @ B @ C ) ) & 
% 8.10/8.29         ( v4_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) ) ))).
% 8.10/8.29  thf('27', plain,
% 8.10/8.29      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.10/8.29         (~ (v4_relat_1 @ X16 @ X17)
% 8.10/8.29          | ~ (v1_relat_1 @ X16)
% 8.10/8.29          | ~ (v1_relat_1 @ X18)
% 8.10/8.29          | (v4_relat_1 @ (k5_relat_1 @ X16 @ X18) @ X17))),
% 8.10/8.29      inference('cnf', [status(esa)], [fc26_relat_1])).
% 8.10/8.29  thf('28', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['26', '27'])).
% 8.10/8.29  thf('29', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ sk_C)
% 8.10/8.29          | ~ (v1_funct_1 @ sk_C)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B))),
% 8.10/8.29      inference('sup-', [status(thm)], ['5', '28'])).
% 8.10/8.29  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('32', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | (v4_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B))),
% 8.10/8.29      inference('demod', [status(thm)], ['29', '30', '31'])).
% 8.10/8.29  thf(t209_relat_1, axiom,
% 8.10/8.29    (![A:$i,B:$i]:
% 8.10/8.29     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 8.10/8.29       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 8.10/8.29  thf('33', plain,
% 8.10/8.29      (![X5 : $i, X6 : $i]:
% 8.10/8.29         (((X5) = (k7_relat_1 @ X5 @ X6))
% 8.10/8.29          | ~ (v4_relat_1 @ X5 @ X6)
% 8.10/8.29          | ~ (v1_relat_1 @ X5))),
% 8.10/8.29      inference('cnf', [status(esa)], [t209_relat_1])).
% 8.10/8.29  thf('34', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0))
% 8.10/8.29          | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0)
% 8.10/8.29              = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ X0) @ sk_B)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['32', '33'])).
% 8.10/8.29  thf('35', plain,
% 8.10/8.29      ((~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)))
% 8.10/8.29        | ~ (v1_relat_1 @ sk_C)
% 8.10/8.29        | ~ (v1_funct_1 @ sk_C)
% 8.10/8.29        | ~ (v2_funct_1 @ sk_C)
% 8.10/8.29        | ((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 8.10/8.29            = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B))
% 8.10/8.29        | ~ (v1_relat_1 @ sk_C))),
% 8.10/8.29      inference('sup-', [status(thm)], ['4', '34'])).
% 8.10/8.29  thf('36', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.10/8.29      inference('sup+', [status(thm)], ['8', '9'])).
% 8.10/8.29  thf(fc4_funct_1, axiom,
% 8.10/8.29    (![A:$i]:
% 8.10/8.29     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 8.10/8.29       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 8.10/8.29  thf('37', plain, (![X19 : $i]: (v1_relat_1 @ (k6_relat_1 @ X19))),
% 8.10/8.29      inference('cnf', [status(esa)], [fc4_funct_1])).
% 8.10/8.29  thf('38', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 8.10/8.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.10/8.29  thf('39', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('40', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('41', plain, ((v1_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('42', plain, ((v2_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('43', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('44', plain,
% 8.10/8.29      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 8.10/8.29         = (k7_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_B))),
% 8.10/8.29      inference('demod', [status(thm)],
% 8.10/8.29                ['35', '36', '39', '40', '41', '42', '43'])).
% 8.10/8.29  thf('45', plain,
% 8.10/8.29      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C)
% 8.10/8.29          = (k7_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_C)) @ sk_B))
% 8.10/8.29        | ~ (v1_relat_1 @ sk_C)
% 8.10/8.29        | ~ (v1_funct_1 @ sk_C)
% 8.10/8.29        | ~ (v2_funct_1 @ sk_C))),
% 8.10/8.29      inference('sup+', [status(thm)], ['3', '44'])).
% 8.10/8.29  thf('46', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.10/8.29      inference('sup+', [status(thm)], ['8', '9'])).
% 8.10/8.29  thf(t29_relset_1, axiom,
% 8.10/8.29    (![A:$i]:
% 8.10/8.29     ( m1_subset_1 @
% 8.10/8.29       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 8.10/8.29  thf('47', plain,
% 8.10/8.29      (![X36 : $i]:
% 8.10/8.29         (m1_subset_1 @ (k6_relat_1 @ X36) @ 
% 8.10/8.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 8.10/8.29      inference('cnf', [status(esa)], [t29_relset_1])).
% 8.10/8.29  thf('48', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 8.10/8.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.10/8.29  thf('49', plain,
% 8.10/8.29      (![X36 : $i]:
% 8.10/8.29         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 8.10/8.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 8.10/8.29      inference('demod', [status(thm)], ['47', '48'])).
% 8.10/8.29  thf(cc2_relset_1, axiom,
% 8.10/8.29    (![A:$i,B:$i,C:$i]:
% 8.10/8.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.10/8.29       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 8.10/8.29  thf('50', plain,
% 8.10/8.29      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.10/8.29         ((v4_relat_1 @ X26 @ X27)
% 8.10/8.29          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 8.10/8.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.10/8.29  thf('51', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 8.10/8.29      inference('sup-', [status(thm)], ['49', '50'])).
% 8.10/8.29  thf('52', plain,
% 8.10/8.29      (![X5 : $i, X6 : $i]:
% 8.10/8.29         (((X5) = (k7_relat_1 @ X5 @ X6))
% 8.10/8.29          | ~ (v4_relat_1 @ X5 @ X6)
% 8.10/8.29          | ~ (v1_relat_1 @ X5))),
% 8.10/8.29      inference('cnf', [status(esa)], [t209_relat_1])).
% 8.10/8.29  thf('53', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 8.10/8.29          | ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['51', '52'])).
% 8.10/8.29  thf('54', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('55', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((k6_partfun1 @ X0) = (k7_relat_1 @ (k6_partfun1 @ X0) @ X0))),
% 8.10/8.29      inference('demod', [status(thm)], ['53', '54'])).
% 8.10/8.29  thf('56', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('57', plain, ((v1_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('58', plain, ((v2_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('59', plain,
% 8.10/8.29      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 8.10/8.29      inference('demod', [status(thm)], ['45', '46', '55', '56', '57', '58'])).
% 8.10/8.29  thf(t80_relat_1, axiom,
% 8.10/8.29    (![A:$i]:
% 8.10/8.29     ( ( v1_relat_1 @ A ) =>
% 8.10/8.29       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 8.10/8.29  thf('60', plain,
% 8.10/8.29      (![X12 : $i]:
% 8.10/8.29         (((k5_relat_1 @ X12 @ (k6_relat_1 @ (k2_relat_1 @ X12))) = (X12))
% 8.10/8.29          | ~ (v1_relat_1 @ X12))),
% 8.10/8.29      inference('cnf', [status(esa)], [t80_relat_1])).
% 8.10/8.29  thf('61', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 8.10/8.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.10/8.29  thf('62', plain,
% 8.10/8.29      (![X12 : $i]:
% 8.10/8.29         (((k5_relat_1 @ X12 @ (k6_partfun1 @ (k2_relat_1 @ X12))) = (X12))
% 8.10/8.29          | ~ (v1_relat_1 @ X12))),
% 8.10/8.29      inference('demod', [status(thm)], ['60', '61'])).
% 8.10/8.29  thf('63', plain,
% 8.10/8.29      (![X12 : $i]:
% 8.10/8.29         (((k5_relat_1 @ X12 @ (k6_partfun1 @ (k2_relat_1 @ X12))) = (X12))
% 8.10/8.29          | ~ (v1_relat_1 @ X12))),
% 8.10/8.29      inference('demod', [status(thm)], ['60', '61'])).
% 8.10/8.29  thf(t55_relat_1, axiom,
% 8.10/8.29    (![A:$i]:
% 8.10/8.29     ( ( v1_relat_1 @ A ) =>
% 8.10/8.29       ( ![B:$i]:
% 8.10/8.29         ( ( v1_relat_1 @ B ) =>
% 8.10/8.29           ( ![C:$i]:
% 8.10/8.29             ( ( v1_relat_1 @ C ) =>
% 8.10/8.29               ( ( k5_relat_1 @ ( k5_relat_1 @ A @ B ) @ C ) =
% 8.10/8.29                 ( k5_relat_1 @ A @ ( k5_relat_1 @ B @ C ) ) ) ) ) ) ) ))).
% 8.10/8.29  thf('64', plain,
% 8.10/8.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X7)
% 8.10/8.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 8.10/8.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 8.10/8.29          | ~ (v1_relat_1 @ X9)
% 8.10/8.29          | ~ (v1_relat_1 @ X8))),
% 8.10/8.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.10/8.29  thf('65', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (((k5_relat_1 @ X0 @ X1)
% 8.10/8.29            = (k5_relat_1 @ X0 @ 
% 8.10/8.29               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)))
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0))))),
% 8.10/8.29      inference('sup+', [status(thm)], ['63', '64'])).
% 8.10/8.29  thf('66', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('67', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (((k5_relat_1 @ X0 @ X1)
% 8.10/8.29            = (k5_relat_1 @ X0 @ 
% 8.10/8.29               (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1)))
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X1))),
% 8.10/8.29      inference('demod', [status(thm)], ['65', '66'])).
% 8.10/8.29  thf('68', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ((k5_relat_1 @ X0 @ X1)
% 8.10/8.29              = (k5_relat_1 @ X0 @ 
% 8.10/8.29                 (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1))))),
% 8.10/8.29      inference('simplify', [status(thm)], ['67'])).
% 8.10/8.29  thf('69', plain,
% 8.10/8.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('70', plain,
% 8.10/8.29      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.10/8.29         ((v4_relat_1 @ X26 @ X27)
% 8.10/8.29          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 8.10/8.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.10/8.29  thf('71', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 8.10/8.29      inference('sup-', [status(thm)], ['69', '70'])).
% 8.10/8.29  thf('72', plain,
% 8.10/8.29      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.10/8.29         (~ (v4_relat_1 @ X16 @ X17)
% 8.10/8.29          | ~ (v1_relat_1 @ X16)
% 8.10/8.29          | ~ (v1_relat_1 @ X18)
% 8.10/8.29          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X18)))),
% 8.10/8.29      inference('cnf', [status(esa)], [fc26_relat_1])).
% 8.10/8.29  thf('73', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k5_relat_1 @ sk_D @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ sk_D))),
% 8.10/8.29      inference('sup-', [status(thm)], ['71', '72'])).
% 8.10/8.29  thf('74', plain,
% 8.10/8.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('75', plain,
% 8.10/8.29      (![X23 : $i, X24 : $i, X25 : $i]:
% 8.10/8.29         ((v1_relat_1 @ X23)
% 8.10/8.29          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 8.10/8.29      inference('cnf', [status(esa)], [cc1_relset_1])).
% 8.10/8.29  thf('76', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('77', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k5_relat_1 @ sk_D @ X0)) | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('demod', [status(thm)], ['73', '76'])).
% 8.10/8.29  thf('78', plain,
% 8.10/8.29      (![X12 : $i]:
% 8.10/8.29         (((k5_relat_1 @ X12 @ (k6_partfun1 @ (k2_relat_1 @ X12))) = (X12))
% 8.10/8.29          | ~ (v1_relat_1 @ X12))),
% 8.10/8.29      inference('demod', [status(thm)], ['60', '61'])).
% 8.10/8.29  thf('79', plain,
% 8.10/8.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X7)
% 8.10/8.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 8.10/8.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 8.10/8.29          | ~ (v1_relat_1 @ X9)
% 8.10/8.29          | ~ (v1_relat_1 @ X8))),
% 8.10/8.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.10/8.29  thf('80', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (((k5_relat_1 @ X1 @ X0)
% 8.10/8.29            = (k5_relat_1 @ X1 @ 
% 8.10/8.29               (k5_relat_1 @ X0 @ 
% 8.10/8.29                (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))))
% 8.10/8.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ 
% 8.10/8.29               (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('sup+', [status(thm)], ['78', '79'])).
% 8.10/8.29  thf('81', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('82', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (((k5_relat_1 @ X1 @ X0)
% 8.10/8.29            = (k5_relat_1 @ X1 @ 
% 8.10/8.29               (k5_relat_1 @ X0 @ 
% 8.10/8.29                (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))))))
% 8.10/8.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('demod', [status(thm)], ['80', '81'])).
% 8.10/8.29  thf('83', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ sk_D)
% 8.10/8.29          | ((k5_relat_1 @ sk_D @ X0)
% 8.10/8.29              = (k5_relat_1 @ sk_D @ 
% 8.10/8.29                 (k5_relat_1 @ X0 @ 
% 8.10/8.29                  (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)))))))),
% 8.10/8.29      inference('sup-', [status(thm)], ['77', '82'])).
% 8.10/8.29  thf('84', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('85', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ((k5_relat_1 @ sk_D @ X0)
% 8.10/8.29              = (k5_relat_1 @ sk_D @ 
% 8.10/8.29                 (k5_relat_1 @ X0 @ 
% 8.10/8.29                  (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ X0)))))))),
% 8.10/8.29      inference('demod', [status(thm)], ['83', '84'])).
% 8.10/8.29  thf('86', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (((k5_relat_1 @ sk_D @ X0)
% 8.10/8.29            = (k5_relat_1 @ sk_D @ 
% 8.10/8.29               (k5_relat_1 @ X0 @ 
% 8.10/8.29                (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ sk_D @ X0))))))
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('simplify', [status(thm)], ['85'])).
% 8.10/8.29  thf('87', plain,
% 8.10/8.29      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 8.10/8.29          = (k5_relat_1 @ sk_D @ 
% 8.10/8.29             (k6_partfun1 @ 
% 8.10/8.29              (k2_relat_1 @ 
% 8.10/8.29               (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))))))
% 8.10/8.29        | ~ (v1_relat_1 @ sk_D)
% 8.10/8.29        | ~ (v1_relat_1 @ 
% 8.10/8.29             (k6_partfun1 @ 
% 8.10/8.29              (k2_relat_1 @ 
% 8.10/8.29               (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))))
% 8.10/8.29        | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 8.10/8.29      inference('sup+', [status(thm)], ['68', '86'])).
% 8.10/8.29  thf('88', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('89', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('90', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('91', plain,
% 8.10/8.29      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 8.10/8.29         = (k5_relat_1 @ sk_D @ 
% 8.10/8.29            (k6_partfun1 @ 
% 8.10/8.29             (k2_relat_1 @ 
% 8.10/8.29              (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))))))),
% 8.10/8.29      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 8.10/8.29  thf('92', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 8.10/8.29      inference('sup-', [status(thm)], ['69', '70'])).
% 8.10/8.29  thf('93', plain,
% 8.10/8.29      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.10/8.29         (~ (v4_relat_1 @ X16 @ X17)
% 8.10/8.29          | ~ (v1_relat_1 @ X16)
% 8.10/8.29          | ~ (v1_relat_1 @ X18)
% 8.10/8.29          | (v4_relat_1 @ (k5_relat_1 @ X16 @ X18) @ X17))),
% 8.10/8.29      inference('cnf', [status(esa)], [fc26_relat_1])).
% 8.10/8.29  thf('94', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((v4_relat_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_B)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ sk_D))),
% 8.10/8.29      inference('sup-', [status(thm)], ['92', '93'])).
% 8.10/8.29  thf('95', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('96', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((v4_relat_1 @ (k5_relat_1 @ sk_D @ X0) @ sk_B) | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('demod', [status(thm)], ['94', '95'])).
% 8.10/8.29  thf('97', plain,
% 8.10/8.29      (((v4_relat_1 @ 
% 8.10/8.29         (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) @ sk_B)
% 8.10/8.29        | ~ (v1_relat_1 @ 
% 8.10/8.29             (k6_partfun1 @ 
% 8.10/8.29              (k2_relat_1 @ 
% 8.10/8.29               (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))))))),
% 8.10/8.29      inference('sup+', [status(thm)], ['91', '96'])).
% 8.10/8.29  thf('98', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('99', plain,
% 8.10/8.29      ((v4_relat_1 @ 
% 8.10/8.29        (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) @ sk_B)),
% 8.10/8.29      inference('demod', [status(thm)], ['97', '98'])).
% 8.10/8.29  thf('100', plain,
% 8.10/8.29      (![X5 : $i, X6 : $i]:
% 8.10/8.29         (((X5) = (k7_relat_1 @ X5 @ X6))
% 8.10/8.29          | ~ (v4_relat_1 @ X5 @ X6)
% 8.10/8.29          | ~ (v1_relat_1 @ X5))),
% 8.10/8.29      inference('cnf', [status(esa)], [t209_relat_1])).
% 8.10/8.29  thf('101', plain,
% 8.10/8.29      ((~ (v1_relat_1 @ 
% 8.10/8.29           (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 8.10/8.29        | ((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 8.10/8.29            = (k7_relat_1 @ 
% 8.10/8.29               (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) @ sk_B)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['99', '100'])).
% 8.10/8.29  thf('102', plain,
% 8.10/8.29      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 8.10/8.29         = (k5_relat_1 @ sk_D @ 
% 8.10/8.29            (k6_partfun1 @ 
% 8.10/8.29             (k2_relat_1 @ 
% 8.10/8.29              (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))))))),
% 8.10/8.29      inference('demod', [status(thm)], ['87', '88', '89', '90'])).
% 8.10/8.29  thf('103', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['14', '15'])).
% 8.10/8.29  thf('104', plain,
% 8.10/8.29      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.10/8.29         (~ (v4_relat_1 @ X16 @ X17)
% 8.10/8.29          | ~ (v1_relat_1 @ X16)
% 8.10/8.29          | ~ (v1_relat_1 @ X18)
% 8.10/8.29          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X18)))),
% 8.10/8.29      inference('cnf', [status(esa)], [fc26_relat_1])).
% 8.10/8.29  thf('105', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('sup-', [status(thm)], ['103', '104'])).
% 8.10/8.29  thf('106', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X1)
% 8.10/8.29          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('simplify', [status(thm)], ['105'])).
% 8.10/8.29  thf('107', plain,
% 8.10/8.29      (((v1_relat_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))
% 8.10/8.29        | ~ (v1_relat_1 @ sk_D)
% 8.10/8.29        | ~ (v1_relat_1 @ 
% 8.10/8.29             (k6_partfun1 @ 
% 8.10/8.29              (k2_relat_1 @ 
% 8.10/8.29               (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))))))),
% 8.10/8.29      inference('sup+', [status(thm)], ['102', '106'])).
% 8.10/8.29  thf('108', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('109', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('110', plain,
% 8.10/8.29      ((v1_relat_1 @ (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 8.10/8.29      inference('demod', [status(thm)], ['107', '108', '109'])).
% 8.10/8.29  thf('111', plain,
% 8.10/8.29      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 8.10/8.29         = (k7_relat_1 @ 
% 8.10/8.29            (k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) @ sk_B))),
% 8.10/8.29      inference('demod', [status(thm)], ['101', '110'])).
% 8.10/8.29  thf('112', plain,
% 8.10/8.29      ((((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D)))
% 8.10/8.29          = (k7_relat_1 @ sk_D @ sk_B))
% 8.10/8.29        | ~ (v1_relat_1 @ sk_D))),
% 8.10/8.29      inference('sup+', [status(thm)], ['62', '111'])).
% 8.10/8.29  thf('113', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 8.10/8.29      inference('sup-', [status(thm)], ['69', '70'])).
% 8.10/8.29  thf('114', plain,
% 8.10/8.29      (![X5 : $i, X6 : $i]:
% 8.10/8.29         (((X5) = (k7_relat_1 @ X5 @ X6))
% 8.10/8.29          | ~ (v4_relat_1 @ X5 @ X6)
% 8.10/8.29          | ~ (v1_relat_1 @ X5))),
% 8.10/8.29      inference('cnf', [status(esa)], [t209_relat_1])).
% 8.10/8.29  thf('115', plain,
% 8.10/8.29      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['113', '114'])).
% 8.10/8.29  thf('116', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('117', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 8.10/8.29      inference('demod', [status(thm)], ['115', '116'])).
% 8.10/8.29  thf('118', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('119', plain,
% 8.10/8.29      (((k5_relat_1 @ sk_D @ (k6_partfun1 @ (k2_relat_1 @ sk_D))) = (sk_D))),
% 8.10/8.29      inference('demod', [status(thm)], ['112', '117', '118'])).
% 8.10/8.29  thf('120', plain, (![X0 : $i]: (v4_relat_1 @ (k6_partfun1 @ X0) @ X0)),
% 8.10/8.29      inference('sup-', [status(thm)], ['49', '50'])).
% 8.10/8.29  thf('121', plain,
% 8.10/8.29      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.10/8.29         (~ (v4_relat_1 @ X16 @ X17)
% 8.10/8.29          | ~ (v1_relat_1 @ X16)
% 8.10/8.29          | ~ (v1_relat_1 @ X18)
% 8.10/8.29          | (v1_relat_1 @ (k5_relat_1 @ X16 @ X18)))),
% 8.10/8.29      inference('cnf', [status(esa)], [fc26_relat_1])).
% 8.10/8.29  thf('122', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['120', '121'])).
% 8.10/8.29  thf('123', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('124', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X1))),
% 8.10/8.29      inference('demod', [status(thm)], ['122', '123'])).
% 8.10/8.29  thf('125', plain,
% 8.10/8.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X7)
% 8.10/8.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 8.10/8.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 8.10/8.29          | ~ (v1_relat_1 @ X9)
% 8.10/8.29          | ~ (v1_relat_1 @ X8))),
% 8.10/8.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.10/8.29  thf('126', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X1)
% 8.10/8.29          | (v1_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('simplify', [status(thm)], ['105'])).
% 8.10/8.29  thf('127', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0)))
% 8.10/8.29          | ~ (v1_relat_1 @ X2)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('sup+', [status(thm)], ['125', '126'])).
% 8.10/8.29  thf('128', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X2)
% 8.10/8.29          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 8.10/8.29      inference('simplify', [status(thm)], ['127'])).
% 8.10/8.29  thf('129', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | (v1_relat_1 @ 
% 8.10/8.29             (k5_relat_1 @ (k6_partfun1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 8.10/8.29          | ~ (v1_relat_1 @ (k6_partfun1 @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X2)
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('sup-', [status(thm)], ['124', '128'])).
% 8.10/8.29  thf('130', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('131', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | (v1_relat_1 @ 
% 8.10/8.29             (k5_relat_1 @ (k6_partfun1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 8.10/8.29          | ~ (v1_relat_1 @ X2)
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('demod', [status(thm)], ['129', '130'])).
% 8.10/8.29  thf('132', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X2)
% 8.10/8.29          | (v1_relat_1 @ 
% 8.10/8.29             (k5_relat_1 @ (k6_partfun1 @ X1) @ (k5_relat_1 @ X0 @ X2)))
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('simplify', [status(thm)], ['131'])).
% 8.10/8.29  thf('133', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))
% 8.10/8.29          | ~ (v1_relat_1 @ sk_D)
% 8.10/8.29          | ~ (v1_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ sk_D))))),
% 8.10/8.29      inference('sup+', [status(thm)], ['119', '132'])).
% 8.10/8.29  thf('134', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('135', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('136', plain,
% 8.10/8.29      (![X0 : $i]: (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 8.10/8.29      inference('demod', [status(thm)], ['133', '134', '135'])).
% 8.10/8.29  thf('137', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ((k5_relat_1 @ X0 @ X1)
% 8.10/8.29              = (k5_relat_1 @ X0 @ 
% 8.10/8.29                 (k5_relat_1 @ (k6_partfun1 @ (k2_relat_1 @ X0)) @ X1))))),
% 8.10/8.29      inference('simplify', [status(thm)], ['67'])).
% 8.10/8.29  thf('138', plain,
% 8.10/8.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X7)
% 8.10/8.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 8.10/8.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 8.10/8.29          | ~ (v1_relat_1 @ X9)
% 8.10/8.29          | ~ (v1_relat_1 @ X8))),
% 8.10/8.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.10/8.29  thf('139', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.29         (((k5_relat_1 @ (k5_relat_1 @ X2 @ X1) @ X0)
% 8.10/8.29            = (k5_relat_1 @ X2 @ 
% 8.10/8.29               (k5_relat_1 @ X1 @ 
% 8.10/8.29                (k5_relat_1 @ 
% 8.10/8.29                 (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ X2 @ X1))) @ X0))))
% 8.10/8.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X2)
% 8.10/8.29          | ~ (v1_relat_1 @ 
% 8.10/8.29               (k5_relat_1 @ 
% 8.10/8.29                (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ X2 @ X1))) @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ X1))),
% 8.10/8.29      inference('sup+', [status(thm)], ['137', '138'])).
% 8.10/8.29  thf('140', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ sk_D)
% 8.10/8.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 8.10/8.29          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ sk_D)
% 8.10/8.29              = (k5_relat_1 @ X1 @ 
% 8.10/8.29                 (k5_relat_1 @ X0 @ 
% 8.10/8.29                  (k5_relat_1 @ 
% 8.10/8.29                   (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ sk_D)))))),
% 8.10/8.29      inference('sup-', [status(thm)], ['136', '139'])).
% 8.10/8.29  thf('141', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('142', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 8.10/8.29          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ sk_D)
% 8.10/8.29              = (k5_relat_1 @ X1 @ 
% 8.10/8.29                 (k5_relat_1 @ X0 @ 
% 8.10/8.29                  (k5_relat_1 @ 
% 8.10/8.29                   (k6_partfun1 @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0))) @ sk_D)))))),
% 8.10/8.29      inference('demod', [status(thm)], ['140', '141'])).
% 8.10/8.29  thf(t94_relat_1, axiom,
% 8.10/8.29    (![A:$i,B:$i]:
% 8.10/8.29     ( ( v1_relat_1 @ B ) =>
% 8.10/8.29       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 8.10/8.29  thf('143', plain,
% 8.10/8.29      (![X13 : $i, X14 : $i]:
% 8.10/8.29         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_relat_1 @ X13) @ X14))
% 8.10/8.29          | ~ (v1_relat_1 @ X14))),
% 8.10/8.29      inference('cnf', [status(esa)], [t94_relat_1])).
% 8.10/8.29  thf('144', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 8.10/8.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.10/8.29  thf('145', plain,
% 8.10/8.29      (![X13 : $i, X14 : $i]:
% 8.10/8.29         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_partfun1 @ X13) @ X14))
% 8.10/8.29          | ~ (v1_relat_1 @ X14))),
% 8.10/8.29      inference('demod', [status(thm)], ['143', '144'])).
% 8.10/8.29  thf('146', plain,
% 8.10/8.29      (![X13 : $i, X14 : $i]:
% 8.10/8.29         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_partfun1 @ X13) @ X14))
% 8.10/8.29          | ~ (v1_relat_1 @ X14))),
% 8.10/8.29      inference('demod', [status(thm)], ['143', '144'])).
% 8.10/8.29  thf(t71_relat_1, axiom,
% 8.10/8.29    (![A:$i]:
% 8.10/8.29     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 8.10/8.29       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 8.10/8.29  thf('147', plain, (![X11 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X11)) = (X11))),
% 8.10/8.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.10/8.29  thf('148', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 8.10/8.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.10/8.29  thf('149', plain,
% 8.10/8.29      (![X11 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X11)) = (X11))),
% 8.10/8.29      inference('demod', [status(thm)], ['147', '148'])).
% 8.10/8.29  thf('150', plain,
% 8.10/8.29      (![X12 : $i]:
% 8.10/8.29         (((k5_relat_1 @ X12 @ (k6_partfun1 @ (k2_relat_1 @ X12))) = (X12))
% 8.10/8.29          | ~ (v1_relat_1 @ X12))),
% 8.10/8.29      inference('demod', [status(thm)], ['60', '61'])).
% 8.10/8.29  thf('151', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 8.10/8.29            = (k6_partfun1 @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 8.10/8.29      inference('sup+', [status(thm)], ['149', '150'])).
% 8.10/8.29  thf('152', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('153', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((k5_relat_1 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))
% 8.10/8.29           = (k6_partfun1 @ X0))),
% 8.10/8.29      inference('demod', [status(thm)], ['151', '152'])).
% 8.10/8.29  thf('154', plain,
% 8.10/8.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X7)
% 8.10/8.29          | ((k5_relat_1 @ (k5_relat_1 @ X8 @ X7) @ X9)
% 8.10/8.29              = (k5_relat_1 @ X8 @ (k5_relat_1 @ X7 @ X9)))
% 8.10/8.29          | ~ (v1_relat_1 @ X9)
% 8.10/8.29          | ~ (v1_relat_1 @ X8))),
% 8.10/8.29      inference('cnf', [status(esa)], [t55_relat_1])).
% 8.10/8.29  thf('155', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (((k5_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 8.10/8.29            = (k5_relat_1 @ (k6_partfun1 @ X0) @ 
% 8.10/8.29               (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)))
% 8.10/8.29          | ~ (v1_relat_1 @ (k6_partfun1 @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ (k6_partfun1 @ X0)))),
% 8.10/8.29      inference('sup+', [status(thm)], ['153', '154'])).
% 8.10/8.29  thf('156', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('157', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('158', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (((k5_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 8.10/8.29            = (k5_relat_1 @ (k6_partfun1 @ X0) @ 
% 8.10/8.29               (k5_relat_1 @ (k6_partfun1 @ X0) @ X1)))
% 8.10/8.29          | ~ (v1_relat_1 @ X1))),
% 8.10/8.29      inference('demod', [status(thm)], ['155', '156', '157'])).
% 8.10/8.29  thf('159', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (((k5_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 8.10/8.29            = (k7_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1) @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X1))),
% 8.10/8.29      inference('sup+', [status(thm)], ['146', '158'])).
% 8.10/8.29  thf('160', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X1))),
% 8.10/8.29      inference('demod', [status(thm)], ['122', '123'])).
% 8.10/8.29  thf('161', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X1)
% 8.10/8.29          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 8.10/8.29              = (k7_relat_1 @ (k5_relat_1 @ (k6_partfun1 @ X0) @ X1) @ X0)))),
% 8.10/8.29      inference('clc', [status(thm)], ['159', '160'])).
% 8.10/8.29  thf('162', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (((k5_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 8.10/8.29            = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ X1))),
% 8.10/8.29      inference('sup+', [status(thm)], ['145', '161'])).
% 8.10/8.29  thf('163', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X1)
% 8.10/8.29          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 8.10/8.29              = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)))),
% 8.10/8.29      inference('simplify', [status(thm)], ['162'])).
% 8.10/8.29  thf('164', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('165', plain,
% 8.10/8.29      (![X13 : $i, X14 : $i]:
% 8.10/8.29         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_partfun1 @ X13) @ X14))
% 8.10/8.29          | ~ (v1_relat_1 @ X14))),
% 8.10/8.29      inference('demod', [status(thm)], ['143', '144'])).
% 8.10/8.29  thf('166', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X1)
% 8.10/8.29          | ((k5_relat_1 @ (k6_partfun1 @ X0) @ X1)
% 8.10/8.29              = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)))),
% 8.10/8.29      inference('simplify', [status(thm)], ['162'])).
% 8.10/8.29  thf('167', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (((k7_relat_1 @ X1 @ X0) = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ X1))),
% 8.10/8.29      inference('sup+', [status(thm)], ['165', '166'])).
% 8.10/8.29  thf('168', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X1)
% 8.10/8.29          | ((k7_relat_1 @ X1 @ X0)
% 8.10/8.29              = (k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X0)))),
% 8.10/8.29      inference('simplify', [status(thm)], ['167'])).
% 8.10/8.29  thf('169', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((k7_relat_1 @ sk_D @ X0)
% 8.10/8.29           = (k7_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 8.10/8.29      inference('sup-', [status(thm)], ['164', '168'])).
% 8.10/8.29  thf('170', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (((k7_relat_1 @ sk_D @ X0) = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))
% 8.10/8.29          | ~ (v1_relat_1 @ sk_D))),
% 8.10/8.29      inference('sup+', [status(thm)], ['163', '169'])).
% 8.10/8.29  thf('171', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('172', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((k7_relat_1 @ sk_D @ X0) = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 8.10/8.29      inference('demod', [status(thm)], ['170', '171'])).
% 8.10/8.29  thf('173', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 8.10/8.29          | ((k5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ sk_D)
% 8.10/8.29              = (k5_relat_1 @ X1 @ 
% 8.10/8.29                 (k5_relat_1 @ X0 @ 
% 8.10/8.29                  (k7_relat_1 @ sk_D @ (k2_relat_1 @ (k5_relat_1 @ X1 @ X0)))))))),
% 8.10/8.29      inference('demod', [status(thm)], ['142', '172'])).
% 8.10/8.29  thf('174', plain,
% 8.10/8.29      ((~ (v1_relat_1 @ (k6_partfun1 @ sk_B))
% 8.10/8.29        | ((k5_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) @ sk_D)
% 8.10/8.29            = (k5_relat_1 @ (k2_funct_1 @ sk_C) @ 
% 8.10/8.29               (k5_relat_1 @ sk_C @ 
% 8.10/8.29                (k7_relat_1 @ sk_D @ 
% 8.10/8.29                 (k2_relat_1 @ (k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C))))))
% 8.10/8.29        | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 8.10/8.29        | ~ (v1_relat_1 @ sk_C))),
% 8.10/8.29      inference('sup-', [status(thm)], ['59', '173'])).
% 8.10/8.29  thf('175', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('176', plain,
% 8.10/8.29      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 8.10/8.29      inference('demod', [status(thm)], ['45', '46', '55', '56', '57', '58'])).
% 8.10/8.29  thf('177', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((k7_relat_1 @ sk_D @ X0) = (k5_relat_1 @ (k6_partfun1 @ X0) @ sk_D))),
% 8.10/8.29      inference('demod', [status(thm)], ['170', '171'])).
% 8.10/8.29  thf('178', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 8.10/8.29      inference('demod', [status(thm)], ['115', '116'])).
% 8.10/8.29  thf('179', plain,
% 8.10/8.29      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ sk_C) = (k6_partfun1 @ sk_B))),
% 8.10/8.29      inference('demod', [status(thm)], ['45', '46', '55', '56', '57', '58'])).
% 8.10/8.29  thf('180', plain,
% 8.10/8.29      (![X11 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X11)) = (X11))),
% 8.10/8.29      inference('demod', [status(thm)], ['147', '148'])).
% 8.10/8.29  thf('181', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 8.10/8.29      inference('demod', [status(thm)], ['115', '116'])).
% 8.10/8.29  thf('182', plain,
% 8.10/8.29      ((r2_relset_1 @ sk_A @ sk_A @ 
% 8.10/8.29        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 8.10/8.29        (k6_partfun1 @ sk_A))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('183', plain,
% 8.10/8.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('184', plain,
% 8.10/8.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf(redefinition_k1_partfun1, axiom,
% 8.10/8.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.10/8.29     ( ( ( v1_funct_1 @ E ) & 
% 8.10/8.29         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.10/8.29         ( v1_funct_1 @ F ) & 
% 8.10/8.29         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 8.10/8.29       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 8.10/8.29  thf('185', plain,
% 8.10/8.29      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 8.10/8.29         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 8.10/8.29          | ~ (v1_funct_1 @ X43)
% 8.10/8.29          | ~ (v1_funct_1 @ X46)
% 8.10/8.29          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 8.10/8.29          | ((k1_partfun1 @ X44 @ X45 @ X47 @ X48 @ X43 @ X46)
% 8.10/8.29              = (k5_relat_1 @ X43 @ X46)))),
% 8.10/8.29      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 8.10/8.29  thf('186', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.29         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 8.10/8.29            = (k5_relat_1 @ sk_C @ X0))
% 8.10/8.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.10/8.29          | ~ (v1_funct_1 @ X0)
% 8.10/8.29          | ~ (v1_funct_1 @ sk_C))),
% 8.10/8.29      inference('sup-', [status(thm)], ['184', '185'])).
% 8.10/8.29  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('188', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.29         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 8.10/8.29            = (k5_relat_1 @ sk_C @ X0))
% 8.10/8.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 8.10/8.29          | ~ (v1_funct_1 @ X0))),
% 8.10/8.29      inference('demod', [status(thm)], ['186', '187'])).
% 8.10/8.29  thf('189', plain,
% 8.10/8.29      ((~ (v1_funct_1 @ sk_D)
% 8.10/8.29        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.10/8.29            = (k5_relat_1 @ sk_C @ sk_D)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['183', '188'])).
% 8.10/8.29  thf('190', plain, ((v1_funct_1 @ sk_D)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('191', plain,
% 8.10/8.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.10/8.29         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.10/8.29      inference('demod', [status(thm)], ['189', '190'])).
% 8.10/8.29  thf('192', plain,
% 8.10/8.29      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 8.10/8.29        (k6_partfun1 @ sk_A))),
% 8.10/8.29      inference('demod', [status(thm)], ['182', '191'])).
% 8.10/8.29  thf('193', plain,
% 8.10/8.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('194', plain,
% 8.10/8.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf(dt_k1_partfun1, axiom,
% 8.10/8.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 8.10/8.29     ( ( ( v1_funct_1 @ E ) & 
% 8.10/8.29         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.10/8.29         ( v1_funct_1 @ F ) & 
% 8.10/8.29         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 8.10/8.29       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 8.10/8.29         ( m1_subset_1 @
% 8.10/8.29           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 8.10/8.29           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 8.10/8.29  thf('195', plain,
% 8.10/8.29      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 8.10/8.29         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 8.10/8.29          | ~ (v1_funct_1 @ X37)
% 8.10/8.29          | ~ (v1_funct_1 @ X40)
% 8.10/8.29          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 8.10/8.29          | (m1_subset_1 @ (k1_partfun1 @ X38 @ X39 @ X41 @ X42 @ X37 @ X40) @ 
% 8.10/8.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X42))))),
% 8.10/8.29      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 8.10/8.29  thf('196', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 8.10/8.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 8.10/8.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 8.10/8.29          | ~ (v1_funct_1 @ X1)
% 8.10/8.29          | ~ (v1_funct_1 @ sk_C))),
% 8.10/8.29      inference('sup-', [status(thm)], ['194', '195'])).
% 8.10/8.29  thf('197', plain, ((v1_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('198', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 8.10/8.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 8.10/8.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 8.10/8.29          | ~ (v1_funct_1 @ X1))),
% 8.10/8.29      inference('demod', [status(thm)], ['196', '197'])).
% 8.10/8.29  thf('199', plain,
% 8.10/8.29      ((~ (v1_funct_1 @ sk_D)
% 8.10/8.29        | (m1_subset_1 @ 
% 8.10/8.29           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 8.10/8.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 8.10/8.29      inference('sup-', [status(thm)], ['193', '198'])).
% 8.10/8.29  thf('200', plain, ((v1_funct_1 @ sk_D)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('201', plain,
% 8.10/8.29      ((m1_subset_1 @ 
% 8.10/8.29        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 8.10/8.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 8.10/8.29      inference('demod', [status(thm)], ['199', '200'])).
% 8.10/8.29  thf('202', plain,
% 8.10/8.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 8.10/8.29         = (k5_relat_1 @ sk_C @ sk_D))),
% 8.10/8.29      inference('demod', [status(thm)], ['189', '190'])).
% 8.10/8.29  thf('203', plain,
% 8.10/8.29      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 8.10/8.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 8.10/8.29      inference('demod', [status(thm)], ['201', '202'])).
% 8.10/8.29  thf(redefinition_r2_relset_1, axiom,
% 8.10/8.29    (![A:$i,B:$i,C:$i,D:$i]:
% 8.10/8.29     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.10/8.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 8.10/8.29       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 8.10/8.29  thf('204', plain,
% 8.10/8.29      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 8.10/8.29         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 8.10/8.29          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 8.10/8.29          | ((X32) = (X35))
% 8.10/8.29          | ~ (r2_relset_1 @ X33 @ X34 @ X32 @ X35))),
% 8.10/8.29      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 8.10/8.29  thf('205', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 8.10/8.29          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 8.10/8.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 8.10/8.29      inference('sup-', [status(thm)], ['203', '204'])).
% 8.10/8.29  thf('206', plain,
% 8.10/8.29      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 8.10/8.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 8.10/8.29        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['192', '205'])).
% 8.10/8.29  thf('207', plain,
% 8.10/8.29      (![X36 : $i]:
% 8.10/8.29         (m1_subset_1 @ (k6_partfun1 @ X36) @ 
% 8.10/8.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X36)))),
% 8.10/8.29      inference('demod', [status(thm)], ['47', '48'])).
% 8.10/8.29  thf('208', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 8.10/8.29      inference('demod', [status(thm)], ['206', '207'])).
% 8.10/8.29  thf('209', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 8.10/8.29      inference('demod', [status(thm)], ['115', '116'])).
% 8.10/8.29  thf('210', plain,
% 8.10/8.29      (![X13 : $i, X14 : $i]:
% 8.10/8.29         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_partfun1 @ X13) @ X14))
% 8.10/8.29          | ~ (v1_relat_1 @ X14))),
% 8.10/8.29      inference('demod', [status(thm)], ['143', '144'])).
% 8.10/8.29  thf('211', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 8.10/8.29      inference('sup+', [status(thm)], ['8', '9'])).
% 8.10/8.29  thf('212', plain,
% 8.10/8.29      (![X12 : $i]:
% 8.10/8.29         (((k5_relat_1 @ X12 @ (k6_partfun1 @ (k2_relat_1 @ X12))) = (X12))
% 8.10/8.29          | ~ (v1_relat_1 @ X12))),
% 8.10/8.29      inference('demod', [status(thm)], ['60', '61'])).
% 8.10/8.29  thf('213', plain,
% 8.10/8.29      ((((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))
% 8.10/8.29        | ~ (v1_relat_1 @ sk_C))),
% 8.10/8.29      inference('sup+', [status(thm)], ['211', '212'])).
% 8.10/8.29  thf('214', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('215', plain, (((k5_relat_1 @ sk_C @ (k6_partfun1 @ sk_B)) = (sk_C))),
% 8.10/8.29      inference('demod', [status(thm)], ['213', '214'])).
% 8.10/8.29  thf('216', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ (k5_relat_1 @ X2 @ X1))
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X2)
% 8.10/8.29          | (v1_relat_1 @ (k5_relat_1 @ X2 @ (k5_relat_1 @ X1 @ X0))))),
% 8.10/8.29      inference('simplify', [status(thm)], ['127'])).
% 8.10/8.29  thf('217', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ sk_C)
% 8.10/8.29          | (v1_relat_1 @ 
% 8.10/8.29             (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 8.10/8.29          | ~ (v1_relat_1 @ sk_C)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ (k6_partfun1 @ sk_B)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['215', '216'])).
% 8.10/8.29  thf('218', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('219', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('220', plain, (![X19 : $i]: (v1_relat_1 @ (k6_partfun1 @ X19))),
% 8.10/8.29      inference('demod', [status(thm)], ['37', '38'])).
% 8.10/8.29  thf('221', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((v1_relat_1 @ 
% 8.10/8.29           (k5_relat_1 @ sk_C @ (k5_relat_1 @ (k6_partfun1 @ sk_B) @ X0)))
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('demod', [status(thm)], ['217', '218', '219', '220'])).
% 8.10/8.29  thf('222', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k5_relat_1 @ sk_C @ (k7_relat_1 @ X0 @ sk_B)))
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('sup+', [status(thm)], ['210', '221'])).
% 8.10/8.29  thf('223', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | (v1_relat_1 @ (k5_relat_1 @ sk_C @ (k7_relat_1 @ X0 @ sk_B))))),
% 8.10/8.29      inference('simplify', [status(thm)], ['222'])).
% 8.10/8.29  thf('224', plain,
% 8.10/8.29      (((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) | ~ (v1_relat_1 @ sk_D))),
% 8.10/8.29      inference('sup+', [status(thm)], ['209', '223'])).
% 8.10/8.29  thf('225', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('226', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))),
% 8.10/8.29      inference('demod', [status(thm)], ['224', '225'])).
% 8.10/8.29  thf('227', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['14', '15'])).
% 8.10/8.29  thf('228', plain,
% 8.10/8.29      (![X16 : $i, X17 : $i, X18 : $i]:
% 8.10/8.29         (~ (v4_relat_1 @ X16 @ X17)
% 8.10/8.29          | ~ (v1_relat_1 @ X16)
% 8.10/8.29          | ~ (v1_relat_1 @ X18)
% 8.10/8.29          | (v4_relat_1 @ (k5_relat_1 @ X16 @ X18) @ X17))),
% 8.10/8.29      inference('cnf', [status(esa)], [fc26_relat_1])).
% 8.10/8.29  thf('229', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | (v4_relat_1 @ (k5_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('sup-', [status(thm)], ['227', '228'])).
% 8.10/8.29  thf('230', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X1)
% 8.10/8.29          | (v4_relat_1 @ (k5_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('simplify', [status(thm)], ['229'])).
% 8.10/8.29  thf('231', plain,
% 8.10/8.29      (![X3 : $i, X4 : $i]:
% 8.10/8.29         (~ (v4_relat_1 @ X3 @ X4)
% 8.10/8.29          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 8.10/8.29          | ~ (v1_relat_1 @ X3))),
% 8.10/8.29      inference('cnf', [status(esa)], [d18_relat_1])).
% 8.10/8.29  thf('232', plain,
% 8.10/8.29      (![X0 : $i, X1 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X1)
% 8.10/8.29          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ X1))
% 8.10/8.29          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) @ 
% 8.10/8.29             (k1_relat_1 @ X0)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['230', '231'])).
% 8.10/8.29  thf('233', plain,
% 8.10/8.29      (((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 8.10/8.29         (k1_relat_1 @ sk_C))
% 8.10/8.29        | ~ (v1_relat_1 @ sk_D)
% 8.10/8.29        | ~ (v1_relat_1 @ sk_C))),
% 8.10/8.29      inference('sup-', [status(thm)], ['226', '232'])).
% 8.10/8.29  thf('234', plain, ((v1_relat_1 @ sk_D)),
% 8.10/8.29      inference('sup-', [status(thm)], ['74', '75'])).
% 8.10/8.29  thf('235', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('236', plain,
% 8.10/8.29      ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)) @ 
% 8.10/8.29        (k1_relat_1 @ sk_C))),
% 8.10/8.29      inference('demod', [status(thm)], ['233', '234', '235'])).
% 8.10/8.29  thf('237', plain,
% 8.10/8.29      (![X0 : $i, X2 : $i]:
% 8.10/8.29         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 8.10/8.29      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.10/8.29  thf('238', plain,
% 8.10/8.29      ((~ (r1_tarski @ (k1_relat_1 @ sk_C) @ 
% 8.10/8.29           (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D)))
% 8.10/8.29        | ((k1_relat_1 @ sk_C) = (k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_D))))),
% 8.10/8.29      inference('sup-', [status(thm)], ['236', '237'])).
% 8.10/8.29  thf('239', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 8.10/8.29      inference('demod', [status(thm)], ['206', '207'])).
% 8.10/8.29  thf('240', plain, (![X10 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 8.10/8.29      inference('cnf', [status(esa)], [t71_relat_1])).
% 8.10/8.29  thf('241', plain, (![X49 : $i]: ((k6_partfun1 @ X49) = (k6_relat_1 @ X49))),
% 8.10/8.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 8.10/8.29  thf('242', plain,
% 8.10/8.29      (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 8.10/8.29      inference('demod', [status(thm)], ['240', '241'])).
% 8.10/8.29  thf('243', plain,
% 8.10/8.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('244', plain,
% 8.10/8.29      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.10/8.29         ((v4_relat_1 @ X26 @ X27)
% 8.10/8.29          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 8.10/8.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 8.10/8.29  thf('245', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 8.10/8.29      inference('sup-', [status(thm)], ['243', '244'])).
% 8.10/8.29  thf('246', plain,
% 8.10/8.29      (![X3 : $i, X4 : $i]:
% 8.10/8.29         (~ (v4_relat_1 @ X3 @ X4)
% 8.10/8.29          | (r1_tarski @ (k1_relat_1 @ X3) @ X4)
% 8.10/8.29          | ~ (v1_relat_1 @ X3))),
% 8.10/8.29      inference('cnf', [status(esa)], [d18_relat_1])).
% 8.10/8.29  thf('247', plain,
% 8.10/8.29      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A))),
% 8.10/8.29      inference('sup-', [status(thm)], ['245', '246'])).
% 8.10/8.29  thf('248', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('249', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 8.10/8.29      inference('demod', [status(thm)], ['247', '248'])).
% 8.10/8.29  thf('250', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_partfun1 @ sk_A))),
% 8.10/8.29      inference('demod', [status(thm)], ['206', '207'])).
% 8.10/8.29  thf('251', plain,
% 8.10/8.29      (![X10 : $i]: ((k1_relat_1 @ (k6_partfun1 @ X10)) = (X10))),
% 8.10/8.29      inference('demod', [status(thm)], ['240', '241'])).
% 8.10/8.29  thf('252', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 8.10/8.29      inference('demod', [status(thm)],
% 8.10/8.29                ['238', '239', '242', '249', '250', '251'])).
% 8.10/8.29  thf('253', plain,
% 8.10/8.29      (![X15 : $i]:
% 8.10/8.29         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 8.10/8.29          | ~ (v1_funct_1 @ X15)
% 8.10/8.29          | ~ (v1_relat_1 @ X15))),
% 8.10/8.29      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 8.10/8.29  thf('254', plain,
% 8.10/8.29      (![X21 : $i]:
% 8.10/8.29         (~ (v2_funct_1 @ X21)
% 8.10/8.29          | ((k1_relat_1 @ X21) = (k2_relat_1 @ (k2_funct_1 @ X21)))
% 8.10/8.29          | ~ (v1_funct_1 @ X21)
% 8.10/8.29          | ~ (v1_relat_1 @ X21))),
% 8.10/8.29      inference('cnf', [status(esa)], [t55_funct_1])).
% 8.10/8.29  thf('255', plain,
% 8.10/8.29      (![X12 : $i]:
% 8.10/8.29         (((k5_relat_1 @ X12 @ (k6_partfun1 @ (k2_relat_1 @ X12))) = (X12))
% 8.10/8.29          | ~ (v1_relat_1 @ X12))),
% 8.10/8.29      inference('demod', [status(thm)], ['60', '61'])).
% 8.10/8.29  thf('256', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.10/8.29            = (k2_funct_1 @ X0))
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_funct_1 @ X0)
% 8.10/8.29          | ~ (v2_funct_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 8.10/8.29      inference('sup+', [status(thm)], ['254', '255'])).
% 8.10/8.29  thf('257', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (~ (v1_relat_1 @ X0)
% 8.10/8.29          | ~ (v1_funct_1 @ X0)
% 8.10/8.29          | ~ (v2_funct_1 @ X0)
% 8.10/8.29          | ~ (v1_funct_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X0)
% 8.10/8.29          | ((k5_relat_1 @ (k2_funct_1 @ X0) @ 
% 8.10/8.29              (k6_partfun1 @ (k1_relat_1 @ X0))) = (k2_funct_1 @ X0)))),
% 8.10/8.29      inference('sup-', [status(thm)], ['253', '256'])).
% 8.10/8.29  thf('258', plain,
% 8.10/8.29      (![X0 : $i]:
% 8.10/8.29         (((k5_relat_1 @ (k2_funct_1 @ X0) @ (k6_partfun1 @ (k1_relat_1 @ X0)))
% 8.10/8.29            = (k2_funct_1 @ X0))
% 8.10/8.29          | ~ (v2_funct_1 @ X0)
% 8.10/8.29          | ~ (v1_funct_1 @ X0)
% 8.10/8.29          | ~ (v1_relat_1 @ X0))),
% 8.10/8.29      inference('simplify', [status(thm)], ['257'])).
% 8.10/8.29  thf('259', plain,
% 8.10/8.29      ((((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 8.10/8.29          = (k2_funct_1 @ sk_C))
% 8.10/8.29        | ~ (v1_relat_1 @ sk_C)
% 8.10/8.29        | ~ (v1_funct_1 @ sk_C)
% 8.10/8.29        | ~ (v2_funct_1 @ sk_C))),
% 8.10/8.29      inference('sup+', [status(thm)], ['252', '258'])).
% 8.10/8.29  thf('260', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('261', plain, ((v1_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('262', plain, ((v2_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('263', plain,
% 8.10/8.29      (((k5_relat_1 @ (k2_funct_1 @ sk_C) @ (k6_partfun1 @ sk_A))
% 8.10/8.29         = (k2_funct_1 @ sk_C))),
% 8.10/8.29      inference('demod', [status(thm)], ['259', '260', '261', '262'])).
% 8.10/8.29  thf('264', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('265', plain,
% 8.10/8.29      ((((sk_D) = (k2_funct_1 @ sk_C)) | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C)))),
% 8.10/8.29      inference('demod', [status(thm)],
% 8.10/8.29                ['174', '175', '176', '177', '178', '179', '180', '181', 
% 8.10/8.29                 '208', '263', '264'])).
% 8.10/8.29  thf('266', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('267', plain, (~ (v1_relat_1 @ (k2_funct_1 @ sk_C))),
% 8.10/8.29      inference('simplify_reflect-', [status(thm)], ['265', '266'])).
% 8.10/8.29  thf('268', plain, ((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C))),
% 8.10/8.29      inference('sup-', [status(thm)], ['0', '267'])).
% 8.10/8.29  thf('269', plain, ((v1_relat_1 @ sk_C)),
% 8.10/8.29      inference('sup-', [status(thm)], ['21', '22'])).
% 8.10/8.29  thf('270', plain, ((v1_funct_1 @ sk_C)),
% 8.10/8.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.10/8.29  thf('271', plain, ($false),
% 8.10/8.29      inference('demod', [status(thm)], ['268', '269', '270'])).
% 8.10/8.29  
% 8.10/8.29  % SZS output end Refutation
% 8.10/8.29  
% 8.10/8.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
