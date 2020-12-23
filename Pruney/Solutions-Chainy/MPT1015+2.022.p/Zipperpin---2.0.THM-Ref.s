%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QpIE0Xw3sn

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:50 EST 2020

% Result     : Theorem 11.57s
% Output     : Refutation 11.57s
% Verified   : 
% Statistics : Number of formulae       :  249 (7145 expanded)
%              Number of leaves         :   44 (2190 expanded)
%              Depth                    :   25
%              Number of atoms          : 2730 (145850 expanded)
%              Number of equality atoms :  102 (1801 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t76_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
              & ( v2_funct_1 @ B ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B )
                & ( v2_funct_1 @ B ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t76_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k1_relset_1 @ X56 @ X56 @ X57 )
        = X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X56 ) ) )
      | ~ ( v1_funct_2 @ X57 @ X56 @ X56 )
      | ~ ( v1_funct_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('5',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X55: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('13',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','18','19'])).

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

thf('21',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X54 @ X53 @ X52 )
       != X53 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X52 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X54 @ X53 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('22',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('25',plain,(
    ! [X55: $i] :
      ( ( v1_funct_2 @ X55 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('26',plain,
    ( ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('28',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','18','19'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['22','23','29','32','33'])).

thf('35',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_B ) @ sk_A ) )
    | ( v1_relat_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t61_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) )
            = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) )
          & ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A )
            = ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X11: $i] :
      ( ~ ( v2_funct_1 @ X11 )
      | ( ( k5_relat_1 @ X11 @ ( k2_funct_1 @ X11 ) )
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t61_funct_1])).

thf('41',plain,(
    ! [X55: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('42',plain,(
    ! [X55: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('43',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 )
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 )
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X55: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('49',plain,(
    ! [X55: $i] :
      ( ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) ) ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X3 @ X2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k1_partfun1 @ ( k1_relat_1 @ X1 ) @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( v1_funct_1 @ ( k6_relat_1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','58'])).

thf('60',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['5','6','7','10'])).

thf('61',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['16','17'])).

thf('62',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['13','18','19'])).

thf('65',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v2_funct_1 @ X52 )
      | ( ( k2_relset_1 @ X54 @ X53 @ X52 )
       != X53 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X52 ) )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X53 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X54 @ X53 )
      | ~ ( v1_funct_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('66',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
     != ( k2_relat_1 @ sk_B ) )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_B @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('69',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('70',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_B ) )
    | ( ( k2_relat_1 @ sk_B )
     != ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('75',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('76',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('77',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
        & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )).

thf('85',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( r2_relset_1 @ X43 @ X44 @ ( k4_relset_1 @ X43 @ X43 @ X43 @ X44 @ ( k6_partfun1 @ X43 ) @ X45 ) @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_funct_2])).

thf('86',plain,(
    ! [X42: $i] :
      ( ( k6_partfun1 @ X42 )
      = ( k6_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('87',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( r2_relset_1 @ X43 @ X44 @ ( k4_relset_1 @ X43 @ X43 @ X43 @ X44 @ ( k6_relat_1 @ X43 ) @ X45 ) @ X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference('sup-',[status(thm)],['84','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('91',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( ( k4_relset_1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21 )
        = ( k5_relat_1 @ X18 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['89','92'])).

thf('94',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['88','93'])).

thf('95',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','72'])).

thf('96',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('98',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ ( k6_relat_1 @ X0 ) @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ sk_B )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ ( k6_relat_1 @ X0 ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','102'])).

thf('104',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf('105',plain,(
    m1_subset_1 @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['103','104'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('106',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['94','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['108','109'])).

thf('111',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['83','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ( ( k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39 )
        = ( k5_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
      = ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','117'])).

thf('119',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('123',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ sk_B ),
    inference(demod,[status(thm)],['121','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('127',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['124','129'])).

thf('131',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = ( k5_relat_1 @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('134',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( X24 = X27 )
      | ~ ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_B ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_B )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_B )
      = sk_B ) ),
    inference('sup-',[status(thm)],['123','136'])).

thf('138',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k5_relat_1 @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B )
    = sk_B ),
    inference(demod,[status(thm)],['120','139'])).

thf('141',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t27_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ( ( v2_funct_1 @ C )
            <=> ! [D: $i,E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( v1_funct_2 @ E @ D @ A )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) )
                 => ! [F: $i] :
                      ( ( ( v1_funct_1 @ F )
                        & ( v1_funct_2 @ F @ D @ A )
                        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) )
                     => ( ( r2_relset_1 @ D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) )
                       => ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) )).

thf('142',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X47 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X47 ) ) )
      | ~ ( r2_relset_1 @ X50 @ X46 @ ( k1_partfun1 @ X50 @ X47 @ X47 @ X46 @ X49 @ X48 ) @ ( k1_partfun1 @ X50 @ X47 @ X47 @ X46 @ X51 @ X48 ) )
      | ( r2_relset_1 @ X50 @ X47 @ X49 @ X51 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X47 ) ) )
      | ~ ( v1_funct_2 @ X51 @ X50 @ X47 )
      | ~ ( v1_funct_1 @ X51 )
      | ~ ( v2_funct_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t27_funct_2])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X2 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['143','144','145','146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_funct_2 @ X2 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( r2_relset_1 @ X1 @ sk_A @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B ) @ ( k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ( r2_relset_1 @ X1 @ sk_A @ X2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['140','148'])).

thf('150',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['149','150','151','152'])).

thf('154',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ~ ( v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['111','153'])).

thf('155',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( r2_relset_1 @ X25 @ X26 @ X24 @ X27 )
      | ( X24 != X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('157',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['155','157'])).

thf('159',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('160',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','72'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('161',plain,(
    ! [X9: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('162',plain,(
    ! [X55: $i] :
      ( ( v1_funct_2 @ X55 @ ( k1_relat_1 @ X55 ) @ ( k2_relat_1 @ X55 ) )
      | ~ ( v1_funct_1 @ X55 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['161','162'])).

thf('164',plain,(
    ! [X10: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X10 ) )
      = X10 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('165',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('166',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('169',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k6_relat_1 @ X0 ) @ X0 @ X0 )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['163','164','169'])).

thf('171',plain,(
    v1_funct_2 @ ( k6_relat_1 @ sk_A ) @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['160','170'])).

thf('172',plain,(
    v1_funct_1 @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['59','60','61','62','63','72'])).

thf('173',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['154','158','159','171','172'])).

thf('174',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k6_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('175',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['173','174'])).

thf('176',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['173','174'])).

thf('177',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['173','174'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('178',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('179',plain,(
    ~ ( r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','175','176','177','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k1_relset_1 @ X56 @ X56 @ X57 )
        = X56 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X56 ) ) )
      | ~ ( v1_funct_2 @ X57 @ X56 @ X56 )
      | ~ ( v1_funct_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('182',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('187',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,
    ( ( k1_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['182','183','184','187'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('189',plain,(
    ! [X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('190',plain,
    ( ( sk_A != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['188','189'])).

thf('191',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('192',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('193',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['191','192'])).

thf('194',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('195',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['193','194'])).

thf('196',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['190','195'])).

thf('197',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['173','174'])).

thf('198',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['196','197'])).

thf('199',plain,(
    sk_C = k1_xboole_0 ),
    inference(simplify,[status(thm)],['198'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('200',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('201',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(simplify,[status(thm)],['156'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['200','201'])).

thf('203',plain,(
    $false ),
    inference(demod,[status(thm)],['179','199','202'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QpIE0Xw3sn
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:59:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 11.57/11.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 11.57/11.80  % Solved by: fo/fo7.sh
% 11.57/11.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 11.57/11.80  % done 12467 iterations in 11.349s
% 11.57/11.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 11.57/11.80  % SZS output start Refutation
% 11.57/11.80  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 11.57/11.80  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 11.57/11.80  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 11.57/11.80  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 11.57/11.80  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 11.57/11.80  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 11.57/11.80  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 11.57/11.80  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 11.57/11.80  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 11.57/11.80  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 11.57/11.80  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 11.57/11.80  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 11.57/11.80  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 11.57/11.80  thf(sk_C_type, type, sk_C: $i).
% 11.57/11.80  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 11.57/11.80  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 11.57/11.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 11.57/11.80  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 11.57/11.80  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 11.57/11.80  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 11.57/11.80  thf(sk_B_type, type, sk_B: $i).
% 11.57/11.80  thf(sk_A_type, type, sk_A: $i).
% 11.57/11.80  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 11.57/11.80  thf(t76_funct_2, conjecture,
% 11.57/11.80    (![A:$i,B:$i]:
% 11.57/11.80     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 11.57/11.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.57/11.80       ( ![C:$i]:
% 11.57/11.80         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 11.57/11.80             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.57/11.80           ( ( ( r2_relset_1 @
% 11.57/11.80                 A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 11.57/11.80               ( v2_funct_1 @ B ) ) =>
% 11.57/11.80             ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 11.57/11.80  thf(zf_stmt_0, negated_conjecture,
% 11.57/11.80    (~( ![A:$i,B:$i]:
% 11.57/11.80        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 11.57/11.80            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.57/11.80          ( ![C:$i]:
% 11.57/11.80            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 11.57/11.80                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.57/11.80              ( ( ( r2_relset_1 @
% 11.57/11.80                    A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ C @ B ) @ B ) & 
% 11.57/11.80                  ( v2_funct_1 @ B ) ) =>
% 11.57/11.80                ( r2_relset_1 @ A @ A @ C @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 11.57/11.80    inference('cnf.neg', [status(esa)], [t76_funct_2])).
% 11.57/11.80  thf('0', plain,
% 11.57/11.80      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_partfun1 @ sk_A))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf(redefinition_k6_partfun1, axiom,
% 11.57/11.80    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 11.57/11.80  thf('1', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 11.57/11.80  thf('2', plain, (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 11.57/11.80      inference('demod', [status(thm)], ['0', '1'])).
% 11.57/11.80  thf('3', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf(t67_funct_2, axiom,
% 11.57/11.80    (![A:$i,B:$i]:
% 11.57/11.80     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 11.57/11.80         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 11.57/11.80       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 11.57/11.80  thf('4', plain,
% 11.57/11.80      (![X56 : $i, X57 : $i]:
% 11.57/11.80         (((k1_relset_1 @ X56 @ X56 @ X57) = (X56))
% 11.57/11.80          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X56)))
% 11.57/11.80          | ~ (v1_funct_2 @ X57 @ X56 @ X56)
% 11.57/11.80          | ~ (v1_funct_1 @ X57))),
% 11.57/11.80      inference('cnf', [status(esa)], [t67_funct_2])).
% 11.57/11.80  thf('5', plain,
% 11.57/11.80      ((~ (v1_funct_1 @ sk_B)
% 11.57/11.80        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.57/11.80        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['3', '4'])).
% 11.57/11.80  thf('6', plain, ((v1_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('7', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('8', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf(redefinition_k1_relset_1, axiom,
% 11.57/11.80    (![A:$i,B:$i,C:$i]:
% 11.57/11.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.57/11.80       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 11.57/11.80  thf('9', plain,
% 11.57/11.80      (![X12 : $i, X13 : $i, X14 : $i]:
% 11.57/11.80         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 11.57/11.80          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 11.57/11.80  thf('10', plain,
% 11.57/11.80      (((k1_relset_1 @ sk_A @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 11.57/11.80      inference('sup-', [status(thm)], ['8', '9'])).
% 11.57/11.80  thf('11', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 11.57/11.80      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 11.57/11.80  thf(t3_funct_2, axiom,
% 11.57/11.80    (![A:$i]:
% 11.57/11.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 11.57/11.80       ( ( v1_funct_1 @ A ) & 
% 11.57/11.80         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 11.57/11.80         ( m1_subset_1 @
% 11.57/11.80           A @ 
% 11.57/11.80           ( k1_zfmisc_1 @
% 11.57/11.80             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 11.57/11.80  thf('12', plain,
% 11.57/11.80      (![X55 : $i]:
% 11.57/11.80         ((m1_subset_1 @ X55 @ 
% 11.57/11.80           (k1_zfmisc_1 @ 
% 11.57/11.80            (k2_zfmisc_1 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 11.57/11.80          | ~ (v1_funct_1 @ X55)
% 11.57/11.80          | ~ (v1_relat_1 @ X55))),
% 11.57/11.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 11.57/11.80  thf('13', plain,
% 11.57/11.80      (((m1_subset_1 @ sk_B @ 
% 11.57/11.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))
% 11.57/11.80        | ~ (v1_relat_1 @ sk_B)
% 11.57/11.80        | ~ (v1_funct_1 @ sk_B))),
% 11.57/11.80      inference('sup+', [status(thm)], ['11', '12'])).
% 11.57/11.80  thf('14', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf(cc2_relat_1, axiom,
% 11.57/11.80    (![A:$i]:
% 11.57/11.80     ( ( v1_relat_1 @ A ) =>
% 11.57/11.80       ( ![B:$i]:
% 11.57/11.80         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 11.57/11.80  thf('15', plain,
% 11.57/11.80      (![X4 : $i, X5 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 11.57/11.80          | (v1_relat_1 @ X4)
% 11.57/11.80          | ~ (v1_relat_1 @ X5))),
% 11.57/11.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 11.57/11.80  thf('16', plain,
% 11.57/11.80      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 11.57/11.80      inference('sup-', [status(thm)], ['14', '15'])).
% 11.57/11.80  thf(fc6_relat_1, axiom,
% 11.57/11.80    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 11.57/11.80  thf('17', plain,
% 11.57/11.80      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 11.57/11.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 11.57/11.80  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 11.57/11.80      inference('demod', [status(thm)], ['16', '17'])).
% 11.57/11.80  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('20', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ 
% 11.57/11.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 11.57/11.80      inference('demod', [status(thm)], ['13', '18', '19'])).
% 11.57/11.80  thf(t31_funct_2, axiom,
% 11.57/11.80    (![A:$i,B:$i,C:$i]:
% 11.57/11.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 11.57/11.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.57/11.80       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 11.57/11.80         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 11.57/11.80           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 11.57/11.80           ( m1_subset_1 @
% 11.57/11.80             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 11.57/11.80  thf('21', plain,
% 11.57/11.80      (![X52 : $i, X53 : $i, X54 : $i]:
% 11.57/11.80         (~ (v2_funct_1 @ X52)
% 11.57/11.80          | ((k2_relset_1 @ X54 @ X53 @ X52) != (X53))
% 11.57/11.80          | (m1_subset_1 @ (k2_funct_1 @ X52) @ 
% 11.57/11.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 11.57/11.80          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53)))
% 11.57/11.80          | ~ (v1_funct_2 @ X52 @ X54 @ X53)
% 11.57/11.80          | ~ (v1_funct_1 @ X52))),
% 11.57/11.80      inference('cnf', [status(esa)], [t31_funct_2])).
% 11.57/11.80  thf('22', plain,
% 11.57/11.80      ((~ (v1_funct_1 @ sk_B)
% 11.57/11.80        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 11.57/11.80        | (m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 11.57/11.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 11.57/11.80        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 11.57/11.80            != (k2_relat_1 @ sk_B))
% 11.57/11.80        | ~ (v2_funct_1 @ sk_B))),
% 11.57/11.80      inference('sup-', [status(thm)], ['20', '21'])).
% 11.57/11.80  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('24', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 11.57/11.80      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 11.57/11.80  thf('25', plain,
% 11.57/11.80      (![X55 : $i]:
% 11.57/11.80         ((v1_funct_2 @ X55 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))
% 11.57/11.80          | ~ (v1_funct_1 @ X55)
% 11.57/11.80          | ~ (v1_relat_1 @ X55))),
% 11.57/11.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 11.57/11.80  thf('26', plain,
% 11.57/11.80      (((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 11.57/11.80        | ~ (v1_relat_1 @ sk_B)
% 11.57/11.80        | ~ (v1_funct_1 @ sk_B))),
% 11.57/11.80      inference('sup+', [status(thm)], ['24', '25'])).
% 11.57/11.80  thf('27', plain, ((v1_relat_1 @ sk_B)),
% 11.57/11.80      inference('demod', [status(thm)], ['16', '17'])).
% 11.57/11.80  thf('28', plain, ((v1_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('29', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 11.57/11.80      inference('demod', [status(thm)], ['26', '27', '28'])).
% 11.57/11.80  thf('30', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ 
% 11.57/11.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 11.57/11.80      inference('demod', [status(thm)], ['13', '18', '19'])).
% 11.57/11.80  thf(redefinition_k2_relset_1, axiom,
% 11.57/11.80    (![A:$i,B:$i,C:$i]:
% 11.57/11.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.57/11.80       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 11.57/11.80  thf('31', plain,
% 11.57/11.80      (![X15 : $i, X16 : $i, X17 : $i]:
% 11.57/11.80         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 11.57/11.80          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 11.57/11.80  thf('32', plain,
% 11.57/11.80      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 11.57/11.80      inference('sup-', [status(thm)], ['30', '31'])).
% 11.57/11.80  thf('33', plain, ((v2_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('34', plain,
% 11.57/11.80      (((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 11.57/11.80         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))
% 11.57/11.80        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 11.57/11.80      inference('demod', [status(thm)], ['22', '23', '29', '32', '33'])).
% 11.57/11.80  thf('35', plain,
% 11.57/11.80      ((m1_subset_1 @ (k2_funct_1 @ sk_B) @ 
% 11.57/11.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 11.57/11.80      inference('simplify', [status(thm)], ['34'])).
% 11.57/11.80  thf('36', plain,
% 11.57/11.80      (![X4 : $i, X5 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 11.57/11.80          | (v1_relat_1 @ X4)
% 11.57/11.80          | ~ (v1_relat_1 @ X5))),
% 11.57/11.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 11.57/11.80  thf('37', plain,
% 11.57/11.80      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_B) @ sk_A))
% 11.57/11.80        | (v1_relat_1 @ (k2_funct_1 @ sk_B)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['35', '36'])).
% 11.57/11.80  thf('38', plain,
% 11.57/11.80      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 11.57/11.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 11.57/11.80  thf('39', plain, ((v1_relat_1 @ (k2_funct_1 @ sk_B))),
% 11.57/11.80      inference('demod', [status(thm)], ['37', '38'])).
% 11.57/11.80  thf(t61_funct_1, axiom,
% 11.57/11.80    (![A:$i]:
% 11.57/11.80     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 11.57/11.80       ( ( v2_funct_1 @ A ) =>
% 11.57/11.80         ( ( ( k5_relat_1 @ A @ ( k2_funct_1 @ A ) ) =
% 11.57/11.80             ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) & 
% 11.57/11.80           ( ( k5_relat_1 @ ( k2_funct_1 @ A ) @ A ) =
% 11.57/11.80             ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 11.57/11.80  thf('40', plain,
% 11.57/11.80      (![X11 : $i]:
% 11.57/11.80         (~ (v2_funct_1 @ X11)
% 11.57/11.80          | ((k5_relat_1 @ X11 @ (k2_funct_1 @ X11))
% 11.57/11.80              = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 11.57/11.80          | ~ (v1_funct_1 @ X11)
% 11.57/11.80          | ~ (v1_relat_1 @ X11))),
% 11.57/11.80      inference('cnf', [status(esa)], [t61_funct_1])).
% 11.57/11.80  thf('41', plain,
% 11.57/11.80      (![X55 : $i]:
% 11.57/11.80         ((m1_subset_1 @ X55 @ 
% 11.57/11.80           (k1_zfmisc_1 @ 
% 11.57/11.80            (k2_zfmisc_1 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 11.57/11.80          | ~ (v1_funct_1 @ X55)
% 11.57/11.80          | ~ (v1_relat_1 @ X55))),
% 11.57/11.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 11.57/11.80  thf('42', plain,
% 11.57/11.80      (![X55 : $i]:
% 11.57/11.80         ((m1_subset_1 @ X55 @ 
% 11.57/11.80           (k1_zfmisc_1 @ 
% 11.57/11.80            (k2_zfmisc_1 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 11.57/11.80          | ~ (v1_funct_1 @ X55)
% 11.57/11.80          | ~ (v1_relat_1 @ X55))),
% 11.57/11.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 11.57/11.80  thf(redefinition_k1_partfun1, axiom,
% 11.57/11.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 11.57/11.80     ( ( ( v1_funct_1 @ E ) & 
% 11.57/11.80         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 11.57/11.80         ( v1_funct_1 @ F ) & 
% 11.57/11.80         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 11.57/11.80       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 11.57/11.80  thf('43', plain,
% 11.57/11.80      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 11.57/11.80          | ~ (v1_funct_1 @ X36)
% 11.57/11.80          | ~ (v1_funct_1 @ X39)
% 11.57/11.80          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 11.57/11.80          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 11.57/11.80              = (k5_relat_1 @ X36 @ X39)))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 11.57/11.80  thf('44', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.57/11.80         (~ (v1_relat_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 11.57/11.80              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 11.57/11.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 11.57/11.80          | ~ (v1_funct_1 @ X1)
% 11.57/11.80          | ~ (v1_funct_1 @ X0))),
% 11.57/11.80      inference('sup-', [status(thm)], ['42', '43'])).
% 11.57/11.80  thf('45', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.57/11.80         (~ (v1_funct_1 @ X1)
% 11.57/11.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 11.57/11.80          | ((k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 11.57/11.80              X0 @ X1) = (k5_relat_1 @ X0 @ X1))
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_relat_1 @ X0))),
% 11.57/11.80      inference('simplify', [status(thm)], ['44'])).
% 11.57/11.80  thf('46', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i]:
% 11.57/11.80         (~ (v1_relat_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_relat_1 @ X1)
% 11.57/11.80          | ~ (v1_funct_1 @ X1)
% 11.57/11.80          | ((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 11.57/11.80              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 11.57/11.80              = (k5_relat_1 @ X1 @ X0))
% 11.57/11.80          | ~ (v1_funct_1 @ X0))),
% 11.57/11.80      inference('sup-', [status(thm)], ['41', '45'])).
% 11.57/11.80  thf('47', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i]:
% 11.57/11.80         (((k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 11.57/11.80            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0)
% 11.57/11.80            = (k5_relat_1 @ X1 @ X0))
% 11.57/11.80          | ~ (v1_funct_1 @ X1)
% 11.57/11.80          | ~ (v1_relat_1 @ X1)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_relat_1 @ X0))),
% 11.57/11.80      inference('simplify', [status(thm)], ['46'])).
% 11.57/11.80  thf('48', plain,
% 11.57/11.80      (![X55 : $i]:
% 11.57/11.80         ((m1_subset_1 @ X55 @ 
% 11.57/11.80           (k1_zfmisc_1 @ 
% 11.57/11.80            (k2_zfmisc_1 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 11.57/11.80          | ~ (v1_funct_1 @ X55)
% 11.57/11.80          | ~ (v1_relat_1 @ X55))),
% 11.57/11.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 11.57/11.80  thf('49', plain,
% 11.57/11.80      (![X55 : $i]:
% 11.57/11.80         ((m1_subset_1 @ X55 @ 
% 11.57/11.80           (k1_zfmisc_1 @ 
% 11.57/11.80            (k2_zfmisc_1 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))))
% 11.57/11.80          | ~ (v1_funct_1 @ X55)
% 11.57/11.80          | ~ (v1_relat_1 @ X55))),
% 11.57/11.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 11.57/11.80  thf(dt_k1_partfun1, axiom,
% 11.57/11.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 11.57/11.80     ( ( ( v1_funct_1 @ E ) & 
% 11.57/11.80         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 11.57/11.80         ( v1_funct_1 @ F ) & 
% 11.57/11.80         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 11.57/11.80       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 11.57/11.80         ( m1_subset_1 @
% 11.57/11.80           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 11.57/11.80           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 11.57/11.80  thf('50', plain,
% 11.57/11.80      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 11.57/11.80          | ~ (v1_funct_1 @ X28)
% 11.57/11.80          | ~ (v1_funct_1 @ X31)
% 11.57/11.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 11.57/11.80          | (v1_funct_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31)))),
% 11.57/11.80      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 11.57/11.80  thf('51', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.57/11.80         (~ (v1_relat_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | (v1_funct_1 @ 
% 11.57/11.80             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 11.57/11.80              X0 @ X1))
% 11.57/11.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 11.57/11.80          | ~ (v1_funct_1 @ X1)
% 11.57/11.80          | ~ (v1_funct_1 @ X0))),
% 11.57/11.80      inference('sup-', [status(thm)], ['49', '50'])).
% 11.57/11.80  thf('52', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.57/11.80         (~ (v1_funct_1 @ X1)
% 11.57/11.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 11.57/11.80          | (v1_funct_1 @ 
% 11.57/11.80             (k1_partfun1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X3 @ X2 @ 
% 11.57/11.80              X0 @ X1))
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_relat_1 @ X0))),
% 11.57/11.80      inference('simplify', [status(thm)], ['51'])).
% 11.57/11.80  thf('53', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i]:
% 11.57/11.80         (~ (v1_relat_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_relat_1 @ X1)
% 11.57/11.80          | ~ (v1_funct_1 @ X1)
% 11.57/11.80          | (v1_funct_1 @ 
% 11.57/11.80             (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 11.57/11.80              (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0))
% 11.57/11.80          | ~ (v1_funct_1 @ X0))),
% 11.57/11.80      inference('sup-', [status(thm)], ['48', '52'])).
% 11.57/11.80  thf('54', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i]:
% 11.57/11.80         ((v1_funct_1 @ 
% 11.57/11.80           (k1_partfun1 @ (k1_relat_1 @ X1) @ (k2_relat_1 @ X1) @ 
% 11.57/11.80            (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X1 @ X0))
% 11.57/11.80          | ~ (v1_funct_1 @ X1)
% 11.57/11.80          | ~ (v1_relat_1 @ X1)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_relat_1 @ X0))),
% 11.57/11.80      inference('simplify', [status(thm)], ['53'])).
% 11.57/11.80  thf('55', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i]:
% 11.57/11.80         ((v1_funct_1 @ (k5_relat_1 @ X1 @ X0))
% 11.57/11.80          | ~ (v1_relat_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_relat_1 @ X1)
% 11.57/11.80          | ~ (v1_funct_1 @ X1)
% 11.57/11.80          | ~ (v1_relat_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_relat_1 @ X1)
% 11.57/11.80          | ~ (v1_funct_1 @ X1))),
% 11.57/11.80      inference('sup+', [status(thm)], ['47', '54'])).
% 11.57/11.80  thf('56', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i]:
% 11.57/11.80         (~ (v1_funct_1 @ X1)
% 11.57/11.80          | ~ (v1_relat_1 @ X1)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_relat_1 @ X0)
% 11.57/11.80          | (v1_funct_1 @ (k5_relat_1 @ X1 @ X0)))),
% 11.57/11.80      inference('simplify', [status(thm)], ['55'])).
% 11.57/11.80  thf('57', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         ((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)))
% 11.57/11.80          | ~ (v1_relat_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v2_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 11.57/11.80          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 11.57/11.80          | ~ (v1_relat_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_1 @ X0))),
% 11.57/11.80      inference('sup+', [status(thm)], ['40', '56'])).
% 11.57/11.80  thf('58', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         (~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 11.57/11.80          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 11.57/11.80          | ~ (v2_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_relat_1 @ X0)
% 11.57/11.80          | (v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ X0))))),
% 11.57/11.80      inference('simplify', [status(thm)], ['57'])).
% 11.57/11.80  thf('59', plain,
% 11.57/11.80      (((v1_funct_1 @ (k6_relat_1 @ (k1_relat_1 @ sk_B)))
% 11.57/11.80        | ~ (v1_relat_1 @ sk_B)
% 11.57/11.80        | ~ (v1_funct_1 @ sk_B)
% 11.57/11.80        | ~ (v2_funct_1 @ sk_B)
% 11.57/11.80        | ~ (v1_funct_1 @ (k2_funct_1 @ sk_B)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['39', '58'])).
% 11.57/11.80  thf('60', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 11.57/11.80      inference('demod', [status(thm)], ['5', '6', '7', '10'])).
% 11.57/11.80  thf('61', plain, ((v1_relat_1 @ sk_B)),
% 11.57/11.80      inference('demod', [status(thm)], ['16', '17'])).
% 11.57/11.80  thf('62', plain, ((v1_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('63', plain, ((v2_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('64', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ 
% 11.57/11.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 11.57/11.80      inference('demod', [status(thm)], ['13', '18', '19'])).
% 11.57/11.80  thf('65', plain,
% 11.57/11.80      (![X52 : $i, X53 : $i, X54 : $i]:
% 11.57/11.80         (~ (v2_funct_1 @ X52)
% 11.57/11.80          | ((k2_relset_1 @ X54 @ X53 @ X52) != (X53))
% 11.57/11.80          | (v1_funct_1 @ (k2_funct_1 @ X52))
% 11.57/11.80          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X53)))
% 11.57/11.80          | ~ (v1_funct_2 @ X52 @ X54 @ X53)
% 11.57/11.80          | ~ (v1_funct_1 @ X52))),
% 11.57/11.80      inference('cnf', [status(esa)], [t31_funct_2])).
% 11.57/11.80  thf('66', plain,
% 11.57/11.80      ((~ (v1_funct_1 @ sk_B)
% 11.57/11.80        | ~ (v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))
% 11.57/11.80        | (v1_funct_1 @ (k2_funct_1 @ sk_B))
% 11.57/11.80        | ((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B)
% 11.57/11.80            != (k2_relat_1 @ sk_B))
% 11.57/11.80        | ~ (v2_funct_1 @ sk_B))),
% 11.57/11.80      inference('sup-', [status(thm)], ['64', '65'])).
% 11.57/11.80  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('68', plain, ((v1_funct_2 @ sk_B @ sk_A @ (k2_relat_1 @ sk_B))),
% 11.57/11.80      inference('demod', [status(thm)], ['26', '27', '28'])).
% 11.57/11.80  thf('69', plain,
% 11.57/11.80      (((k2_relset_1 @ sk_A @ (k2_relat_1 @ sk_B) @ sk_B) = (k2_relat_1 @ sk_B))),
% 11.57/11.80      inference('sup-', [status(thm)], ['30', '31'])).
% 11.57/11.80  thf('70', plain, ((v2_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('71', plain,
% 11.57/11.80      (((v1_funct_1 @ (k2_funct_1 @ sk_B))
% 11.57/11.80        | ((k2_relat_1 @ sk_B) != (k2_relat_1 @ sk_B)))),
% 11.57/11.80      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 11.57/11.80  thf('72', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_B))),
% 11.57/11.80      inference('simplify', [status(thm)], ['71'])).
% 11.57/11.80  thf('73', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 11.57/11.80      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '72'])).
% 11.57/11.80  thf('74', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf(dt_k6_partfun1, axiom,
% 11.57/11.80    (![A:$i]:
% 11.57/11.80     ( ( m1_subset_1 @
% 11.57/11.80         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 11.57/11.80       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 11.57/11.80  thf('75', plain,
% 11.57/11.80      (![X35 : $i]:
% 11.57/11.80         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 11.57/11.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 11.57/11.80      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 11.57/11.80  thf('76', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 11.57/11.80  thf('77', plain,
% 11.57/11.80      (![X35 : $i]:
% 11.57/11.80         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 11.57/11.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 11.57/11.80      inference('demod', [status(thm)], ['75', '76'])).
% 11.57/11.80  thf('78', plain,
% 11.57/11.80      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 11.57/11.80          | ~ (v1_funct_1 @ X36)
% 11.57/11.80          | ~ (v1_funct_1 @ X39)
% 11.57/11.80          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 11.57/11.80          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 11.57/11.80              = (k5_relat_1 @ X36 @ X39)))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 11.57/11.80  thf('79', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.57/11.80         (((k1_partfun1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 11.57/11.80            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 11.57/11.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2)))
% 11.57/11.80          | ~ (v1_funct_1 @ X1)
% 11.57/11.80          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['77', '78'])).
% 11.57/11.80  thf('80', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 11.57/11.80          | ~ (v1_funct_1 @ sk_B)
% 11.57/11.80          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 11.57/11.80              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['74', '79'])).
% 11.57/11.80  thf('81', plain, ((v1_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('82', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 11.57/11.80          | ((k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 11.57/11.80              = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B)))),
% 11.57/11.80      inference('demod', [status(thm)], ['80', '81'])).
% 11.57/11.80  thf('83', plain,
% 11.57/11.80      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 11.57/11.80         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 11.57/11.80      inference('sup-', [status(thm)], ['73', '82'])).
% 11.57/11.80  thf('84', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf(t23_funct_2, axiom,
% 11.57/11.80    (![A:$i,B:$i,C:$i]:
% 11.57/11.80     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 11.57/11.80       ( ( r2_relset_1 @
% 11.57/11.80           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 11.57/11.80           C ) & 
% 11.57/11.80         ( r2_relset_1 @
% 11.57/11.80           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 11.57/11.80           C ) ) ))).
% 11.57/11.80  thf('85', plain,
% 11.57/11.80      (![X43 : $i, X44 : $i, X45 : $i]:
% 11.57/11.80         ((r2_relset_1 @ X43 @ X44 @ 
% 11.57/11.80           (k4_relset_1 @ X43 @ X43 @ X43 @ X44 @ (k6_partfun1 @ X43) @ X45) @ 
% 11.57/11.80           X45)
% 11.57/11.80          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 11.57/11.80      inference('cnf', [status(esa)], [t23_funct_2])).
% 11.57/11.80  thf('86', plain, (![X42 : $i]: ((k6_partfun1 @ X42) = (k6_relat_1 @ X42))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 11.57/11.80  thf('87', plain,
% 11.57/11.80      (![X43 : $i, X44 : $i, X45 : $i]:
% 11.57/11.80         ((r2_relset_1 @ X43 @ X44 @ 
% 11.57/11.80           (k4_relset_1 @ X43 @ X43 @ X43 @ X44 @ (k6_relat_1 @ X43) @ X45) @ 
% 11.57/11.80           X45)
% 11.57/11.80          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 11.57/11.80      inference('demod', [status(thm)], ['85', '86'])).
% 11.57/11.80  thf('88', plain,
% 11.57/11.80      ((r2_relset_1 @ sk_A @ sk_A @ 
% 11.57/11.80        (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 11.57/11.80        sk_B)),
% 11.57/11.80      inference('sup-', [status(thm)], ['84', '87'])).
% 11.57/11.80  thf('89', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('90', plain,
% 11.57/11.80      (![X35 : $i]:
% 11.57/11.80         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 11.57/11.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 11.57/11.80      inference('demod', [status(thm)], ['75', '76'])).
% 11.57/11.80  thf(redefinition_k4_relset_1, axiom,
% 11.57/11.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 11.57/11.80     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 11.57/11.80         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 11.57/11.80       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 11.57/11.80  thf('91', plain,
% 11.57/11.80      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 11.57/11.80          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 11.57/11.80          | ((k4_relset_1 @ X19 @ X20 @ X22 @ X23 @ X18 @ X21)
% 11.57/11.80              = (k5_relat_1 @ X18 @ X21)))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 11.57/11.80  thf('92', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.57/11.80         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 11.57/11.80            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 11.57/11.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 11.57/11.80      inference('sup-', [status(thm)], ['90', '91'])).
% 11.57/11.80  thf('93', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B)
% 11.57/11.80           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B))),
% 11.57/11.80      inference('sup-', [status(thm)], ['89', '92'])).
% 11.57/11.80  thf('94', plain,
% 11.57/11.80      ((r2_relset_1 @ sk_A @ sk_A @ 
% 11.57/11.80        (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ sk_B)),
% 11.57/11.80      inference('demod', [status(thm)], ['88', '93'])).
% 11.57/11.80  thf('95', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 11.57/11.80      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '72'])).
% 11.57/11.80  thf('96', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('97', plain,
% 11.57/11.80      (![X35 : $i]:
% 11.57/11.80         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 11.57/11.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 11.57/11.80      inference('demod', [status(thm)], ['75', '76'])).
% 11.57/11.80  thf('98', plain,
% 11.57/11.80      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 11.57/11.80          | ~ (v1_funct_1 @ X28)
% 11.57/11.80          | ~ (v1_funct_1 @ X31)
% 11.57/11.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 11.57/11.80          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 11.57/11.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 11.57/11.80      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 11.57/11.80  thf('99', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 11.57/11.80         ((m1_subset_1 @ 
% 11.57/11.80           (k1_partfun1 @ X0 @ X0 @ X3 @ X1 @ (k6_relat_1 @ X0) @ X2) @ 
% 11.57/11.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 11.57/11.80          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X1)))
% 11.57/11.80          | ~ (v1_funct_1 @ X2)
% 11.57/11.80          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['97', '98'])).
% 11.57/11.80  thf('100', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 11.57/11.80          | ~ (v1_funct_1 @ sk_B)
% 11.57/11.80          | (m1_subset_1 @ 
% 11.57/11.80             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 11.57/11.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 11.57/11.80      inference('sup-', [status(thm)], ['96', '99'])).
% 11.57/11.80  thf('101', plain, ((v1_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('102', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         (~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 11.57/11.80          | (m1_subset_1 @ 
% 11.57/11.80             (k1_partfun1 @ X0 @ X0 @ sk_A @ sk_A @ (k6_relat_1 @ X0) @ sk_B) @ 
% 11.57/11.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A))))),
% 11.57/11.80      inference('demod', [status(thm)], ['100', '101'])).
% 11.57/11.80  thf('103', plain,
% 11.57/11.80      ((m1_subset_1 @ 
% 11.57/11.80        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 11.57/11.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['95', '102'])).
% 11.57/11.80  thf('104', plain,
% 11.57/11.80      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 11.57/11.80         = (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B))),
% 11.57/11.80      inference('sup-', [status(thm)], ['73', '82'])).
% 11.57/11.80  thf('105', plain,
% 11.57/11.80      ((m1_subset_1 @ (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ 
% 11.57/11.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('demod', [status(thm)], ['103', '104'])).
% 11.57/11.80  thf(redefinition_r2_relset_1, axiom,
% 11.57/11.80    (![A:$i,B:$i,C:$i,D:$i]:
% 11.57/11.80     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 11.57/11.80         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.57/11.80       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 11.57/11.80  thf('106', plain,
% 11.57/11.80      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 11.57/11.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 11.57/11.80          | ((X24) = (X27))
% 11.57/11.80          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 11.57/11.80  thf('107', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 11.57/11.80             (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) @ X0)
% 11.57/11.80          | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (X0))
% 11.57/11.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 11.57/11.80      inference('sup-', [status(thm)], ['105', '106'])).
% 11.57/11.80  thf('108', plain,
% 11.57/11.80      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.57/11.80        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['94', '107'])).
% 11.57/11.80  thf('109', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('110', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))),
% 11.57/11.80      inference('demod', [status(thm)], ['108', '109'])).
% 11.57/11.80  thf('111', plain,
% 11.57/11.80      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ sk_B)
% 11.57/11.80         = (sk_B))),
% 11.57/11.80      inference('demod', [status(thm)], ['83', '110'])).
% 11.57/11.80  thf('112', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('113', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('114', plain,
% 11.57/11.80      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 11.57/11.80          | ~ (v1_funct_1 @ X36)
% 11.57/11.80          | ~ (v1_funct_1 @ X39)
% 11.57/11.80          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 11.57/11.80          | ((k1_partfun1 @ X37 @ X38 @ X40 @ X41 @ X36 @ X39)
% 11.57/11.80              = (k5_relat_1 @ X36 @ X39)))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 11.57/11.80  thf('115', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.57/11.80         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 11.57/11.80            = (k5_relat_1 @ sk_C @ X0))
% 11.57/11.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_1 @ sk_C))),
% 11.57/11.80      inference('sup-', [status(thm)], ['113', '114'])).
% 11.57/11.80  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('117', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.57/11.80         (((k1_partfun1 @ sk_A @ sk_A @ X2 @ X1 @ sk_C @ X0)
% 11.57/11.80            = (k5_relat_1 @ sk_C @ X0))
% 11.57/11.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 11.57/11.80          | ~ (v1_funct_1 @ X0))),
% 11.57/11.80      inference('demod', [status(thm)], ['115', '116'])).
% 11.57/11.80  thf('118', plain,
% 11.57/11.80      ((~ (v1_funct_1 @ sk_B)
% 11.57/11.80        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 11.57/11.80            = (k5_relat_1 @ sk_C @ sk_B)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['112', '117'])).
% 11.57/11.80  thf('119', plain, ((v1_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('120', plain,
% 11.57/11.80      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 11.57/11.80         = (k5_relat_1 @ sk_C @ sk_B))),
% 11.57/11.80      inference('demod', [status(thm)], ['118', '119'])).
% 11.57/11.80  thf('121', plain,
% 11.57/11.80      ((r2_relset_1 @ sk_A @ sk_A @ 
% 11.57/11.80        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('122', plain,
% 11.57/11.80      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 11.57/11.80         = (k5_relat_1 @ sk_C @ sk_B))),
% 11.57/11.80      inference('demod', [status(thm)], ['118', '119'])).
% 11.57/11.80  thf('123', plain,
% 11.57/11.80      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ sk_B)),
% 11.57/11.80      inference('demod', [status(thm)], ['121', '122'])).
% 11.57/11.80  thf('124', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('125', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('126', plain,
% 11.57/11.80      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 11.57/11.80          | ~ (v1_funct_1 @ X28)
% 11.57/11.80          | ~ (v1_funct_1 @ X31)
% 11.57/11.80          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 11.57/11.80          | (m1_subset_1 @ (k1_partfun1 @ X29 @ X30 @ X32 @ X33 @ X28 @ X31) @ 
% 11.57/11.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X33))))),
% 11.57/11.80      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 11.57/11.80  thf('127', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.57/11.80         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 11.57/11.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 11.57/11.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 11.57/11.80          | ~ (v1_funct_1 @ X1)
% 11.57/11.80          | ~ (v1_funct_1 @ sk_C))),
% 11.57/11.80      inference('sup-', [status(thm)], ['125', '126'])).
% 11.57/11.80  thf('128', plain, ((v1_funct_1 @ sk_C)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('129', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.57/11.80         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_C @ X1) @ 
% 11.57/11.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 11.57/11.80          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 11.57/11.80          | ~ (v1_funct_1 @ X1))),
% 11.57/11.80      inference('demod', [status(thm)], ['127', '128'])).
% 11.57/11.80  thf('130', plain,
% 11.57/11.80      ((~ (v1_funct_1 @ sk_B)
% 11.57/11.80        | (m1_subset_1 @ 
% 11.57/11.80           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 11.57/11.80           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 11.57/11.80      inference('sup-', [status(thm)], ['124', '129'])).
% 11.57/11.80  thf('131', plain, ((v1_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('132', plain,
% 11.57/11.80      ((m1_subset_1 @ 
% 11.57/11.80        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) @ 
% 11.57/11.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('demod', [status(thm)], ['130', '131'])).
% 11.57/11.80  thf('133', plain,
% 11.57/11.80      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B)
% 11.57/11.80         = (k5_relat_1 @ sk_C @ sk_B))),
% 11.57/11.80      inference('demod', [status(thm)], ['118', '119'])).
% 11.57/11.80  thf('134', plain,
% 11.57/11.80      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_B) @ 
% 11.57/11.80        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('demod', [status(thm)], ['132', '133'])).
% 11.57/11.80  thf('135', plain,
% 11.57/11.80      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 11.57/11.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 11.57/11.80          | ((X24) = (X27))
% 11.57/11.80          | ~ (r2_relset_1 @ X25 @ X26 @ X24 @ X27))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 11.57/11.80  thf('136', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_B) @ X0)
% 11.57/11.80          | ((k5_relat_1 @ sk_C @ sk_B) = (X0))
% 11.57/11.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 11.57/11.80      inference('sup-', [status(thm)], ['134', '135'])).
% 11.57/11.80  thf('137', plain,
% 11.57/11.80      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.57/11.80        | ((k5_relat_1 @ sk_C @ sk_B) = (sk_B)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['123', '136'])).
% 11.57/11.80  thf('138', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('139', plain, (((k5_relat_1 @ sk_C @ sk_B) = (sk_B))),
% 11.57/11.80      inference('demod', [status(thm)], ['137', '138'])).
% 11.57/11.80  thf('140', plain,
% 11.57/11.80      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_C @ sk_B) = (sk_B))),
% 11.57/11.80      inference('demod', [status(thm)], ['120', '139'])).
% 11.57/11.80  thf('141', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf(t27_funct_2, axiom,
% 11.57/11.80    (![A:$i,B:$i,C:$i]:
% 11.57/11.80     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 11.57/11.80         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 11.57/11.80       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 11.57/11.80            ( ~( ( v2_funct_1 @ C ) <=>
% 11.57/11.80                 ( ![D:$i,E:$i]:
% 11.57/11.80                   ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ D @ A ) & 
% 11.57/11.80                       ( m1_subset_1 @
% 11.57/11.80                         E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 11.57/11.80                     ( ![F:$i]:
% 11.57/11.80                       ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ A ) & 
% 11.57/11.80                           ( m1_subset_1 @
% 11.57/11.80                             F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ A ) ) ) ) =>
% 11.57/11.80                         ( ( r2_relset_1 @
% 11.57/11.80                             D @ B @ ( k1_partfun1 @ D @ A @ A @ B @ E @ C ) @ 
% 11.57/11.80                             ( k1_partfun1 @ D @ A @ A @ B @ F @ C ) ) =>
% 11.57/11.80                           ( r2_relset_1 @ D @ A @ E @ F ) ) ) ) ) ) ) ) ) ) ))).
% 11.57/11.80  thf('142', plain,
% 11.57/11.80      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 11.57/11.80         (((X46) = (k1_xboole_0))
% 11.57/11.80          | ((X47) = (k1_xboole_0))
% 11.57/11.80          | ~ (v1_funct_1 @ X48)
% 11.57/11.80          | ~ (v1_funct_2 @ X48 @ X47 @ X46)
% 11.57/11.80          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 11.57/11.80          | ~ (v1_funct_1 @ X49)
% 11.57/11.80          | ~ (v1_funct_2 @ X49 @ X50 @ X47)
% 11.57/11.80          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X47)))
% 11.57/11.80          | ~ (r2_relset_1 @ X50 @ X46 @ 
% 11.57/11.80               (k1_partfun1 @ X50 @ X47 @ X47 @ X46 @ X49 @ X48) @ 
% 11.57/11.80               (k1_partfun1 @ X50 @ X47 @ X47 @ X46 @ X51 @ X48))
% 11.57/11.80          | (r2_relset_1 @ X50 @ X47 @ X49 @ X51)
% 11.57/11.80          | ~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X47)))
% 11.57/11.80          | ~ (v1_funct_2 @ X51 @ X50 @ X47)
% 11.57/11.80          | ~ (v1_funct_1 @ X51)
% 11.57/11.80          | ~ (v2_funct_1 @ X48))),
% 11.57/11.80      inference('cnf', [status(esa)], [t27_funct_2])).
% 11.57/11.80  thf('143', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.57/11.80         (~ (v2_funct_1 @ sk_B)
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 11.57/11.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 11.57/11.80          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 11.57/11.80          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 11.57/11.80               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 11.57/11.80               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 11.57/11.80          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 11.57/11.80          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 11.57/11.80          | ~ (v1_funct_1 @ X2)
% 11.57/11.80          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 11.57/11.80          | ~ (v1_funct_1 @ sk_B)
% 11.57/11.80          | ((sk_A) = (k1_xboole_0))
% 11.57/11.80          | ((sk_A) = (k1_xboole_0)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['141', '142'])).
% 11.57/11.80  thf('144', plain, ((v2_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('145', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('146', plain, ((v1_funct_1 @ sk_B)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('147', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.57/11.80         (~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 11.57/11.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 11.57/11.80          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 11.57/11.80          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 11.57/11.80               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 11.57/11.80               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 11.57/11.80          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 11.57/11.80          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 11.57/11.80          | ~ (v1_funct_1 @ X2)
% 11.57/11.80          | ((sk_A) = (k1_xboole_0))
% 11.57/11.80          | ((sk_A) = (k1_xboole_0)))),
% 11.57/11.80      inference('demod', [status(thm)], ['143', '144', '145', '146'])).
% 11.57/11.80  thf('148', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 11.57/11.80         (((sk_A) = (k1_xboole_0))
% 11.57/11.80          | ~ (v1_funct_1 @ X2)
% 11.57/11.80          | ~ (v1_funct_2 @ X2 @ X1 @ sk_A)
% 11.57/11.80          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 11.57/11.80          | ~ (r2_relset_1 @ X1 @ sk_A @ 
% 11.57/11.80               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X2 @ sk_B) @ 
% 11.57/11.80               (k1_partfun1 @ X1 @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 11.57/11.80          | (r2_relset_1 @ X1 @ sk_A @ X2 @ X0)
% 11.57/11.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_A)))
% 11.57/11.80          | ~ (v1_funct_2 @ X0 @ X1 @ sk_A)
% 11.57/11.80          | ~ (v1_funct_1 @ X0))),
% 11.57/11.80      inference('simplify', [status(thm)], ['147'])).
% 11.57/11.80  thf('149', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 11.57/11.80             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 11.57/11.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.57/11.80          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 11.57/11.80          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.57/11.80          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 11.57/11.80          | ~ (v1_funct_1 @ sk_C)
% 11.57/11.80          | ((sk_A) = (k1_xboole_0)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['140', '148'])).
% 11.57/11.80  thf('150', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('151', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('152', plain, ((v1_funct_1 @ sk_C)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('153', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ 
% 11.57/11.80             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_B))
% 11.57/11.80          | ~ (v1_funct_1 @ X0)
% 11.57/11.80          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 11.57/11.80          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.57/11.80          | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 11.57/11.80          | ((sk_A) = (k1_xboole_0)))),
% 11.57/11.80      inference('demod', [status(thm)], ['149', '150', '151', '152'])).
% 11.57/11.80  thf('154', plain,
% 11.57/11.80      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)
% 11.57/11.80        | ((sk_A) = (k1_xboole_0))
% 11.57/11.80        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))
% 11.57/11.80        | ~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 11.57/11.80             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 11.57/11.80        | ~ (v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)
% 11.57/11.80        | ~ (v1_funct_1 @ (k6_relat_1 @ sk_A)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['111', '153'])).
% 11.57/11.80  thf('155', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('156', plain,
% 11.57/11.80      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 11.57/11.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 11.57/11.80          | (r2_relset_1 @ X25 @ X26 @ X24 @ X27)
% 11.57/11.80          | ((X24) != (X27)))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 11.57/11.80  thf('157', plain,
% 11.57/11.80      (![X25 : $i, X26 : $i, X27 : $i]:
% 11.57/11.80         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 11.57/11.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 11.57/11.80      inference('simplify', [status(thm)], ['156'])).
% 11.57/11.80  thf('158', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 11.57/11.80      inference('sup-', [status(thm)], ['155', '157'])).
% 11.57/11.80  thf('159', plain,
% 11.57/11.80      (![X35 : $i]:
% 11.57/11.80         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 11.57/11.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 11.57/11.80      inference('demod', [status(thm)], ['75', '76'])).
% 11.57/11.80  thf('160', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 11.57/11.80      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '72'])).
% 11.57/11.80  thf(t71_relat_1, axiom,
% 11.57/11.80    (![A:$i]:
% 11.57/11.80     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 11.57/11.80       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 11.57/11.80  thf('161', plain, (![X9 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 11.57/11.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.57/11.80  thf('162', plain,
% 11.57/11.80      (![X55 : $i]:
% 11.57/11.80         ((v1_funct_2 @ X55 @ (k1_relat_1 @ X55) @ (k2_relat_1 @ X55))
% 11.57/11.80          | ~ (v1_funct_1 @ X55)
% 11.57/11.80          | ~ (v1_relat_1 @ X55))),
% 11.57/11.80      inference('cnf', [status(esa)], [t3_funct_2])).
% 11.57/11.80  thf('163', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ 
% 11.57/11.80           (k2_relat_1 @ (k6_relat_1 @ X0)))
% 11.57/11.80          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 11.57/11.80          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 11.57/11.80      inference('sup+', [status(thm)], ['161', '162'])).
% 11.57/11.80  thf('164', plain, (![X10 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X10)) = (X10))),
% 11.57/11.80      inference('cnf', [status(esa)], [t71_relat_1])).
% 11.57/11.80  thf('165', plain,
% 11.57/11.80      (![X35 : $i]:
% 11.57/11.80         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 11.57/11.80          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 11.57/11.80      inference('demod', [status(thm)], ['75', '76'])).
% 11.57/11.80  thf('166', plain,
% 11.57/11.80      (![X4 : $i, X5 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 11.57/11.80          | (v1_relat_1 @ X4)
% 11.57/11.80          | ~ (v1_relat_1 @ X5))),
% 11.57/11.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 11.57/11.80  thf('167', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X0))
% 11.57/11.80          | (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['165', '166'])).
% 11.57/11.80  thf('168', plain,
% 11.57/11.80      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 11.57/11.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 11.57/11.80  thf('169', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 11.57/11.80      inference('demod', [status(thm)], ['167', '168'])).
% 11.57/11.80  thf('170', plain,
% 11.57/11.80      (![X0 : $i]:
% 11.57/11.80         ((v1_funct_2 @ (k6_relat_1 @ X0) @ X0 @ X0)
% 11.57/11.80          | ~ (v1_funct_1 @ (k6_relat_1 @ X0)))),
% 11.57/11.80      inference('demod', [status(thm)], ['163', '164', '169'])).
% 11.57/11.80  thf('171', plain, ((v1_funct_2 @ (k6_relat_1 @ sk_A) @ sk_A @ sk_A)),
% 11.57/11.80      inference('sup-', [status(thm)], ['160', '170'])).
% 11.57/11.80  thf('172', plain, ((v1_funct_1 @ (k6_relat_1 @ sk_A))),
% 11.57/11.80      inference('demod', [status(thm)], ['59', '60', '61', '62', '63', '72'])).
% 11.57/11.80  thf('173', plain,
% 11.57/11.80      ((((sk_A) = (k1_xboole_0))
% 11.57/11.80        | (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A)))),
% 11.57/11.80      inference('demod', [status(thm)], ['154', '158', '159', '171', '172'])).
% 11.57/11.80  thf('174', plain,
% 11.57/11.80      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k6_relat_1 @ sk_A))),
% 11.57/11.80      inference('demod', [status(thm)], ['0', '1'])).
% 11.57/11.80  thf('175', plain, (((sk_A) = (k1_xboole_0))),
% 11.57/11.80      inference('clc', [status(thm)], ['173', '174'])).
% 11.57/11.80  thf('176', plain, (((sk_A) = (k1_xboole_0))),
% 11.57/11.80      inference('clc', [status(thm)], ['173', '174'])).
% 11.57/11.80  thf('177', plain, (((sk_A) = (k1_xboole_0))),
% 11.57/11.80      inference('clc', [status(thm)], ['173', '174'])).
% 11.57/11.80  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 11.57/11.80  thf('178', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 11.57/11.80      inference('cnf', [status(esa)], [t81_relat_1])).
% 11.57/11.80  thf('179', plain,
% 11.57/11.80      (~ (r2_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_C @ k1_xboole_0)),
% 11.57/11.80      inference('demod', [status(thm)], ['2', '175', '176', '177', '178'])).
% 11.57/11.80  thf('180', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('181', plain,
% 11.57/11.80      (![X56 : $i, X57 : $i]:
% 11.57/11.80         (((k1_relset_1 @ X56 @ X56 @ X57) = (X56))
% 11.57/11.80          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X56)))
% 11.57/11.80          | ~ (v1_funct_2 @ X57 @ X56 @ X56)
% 11.57/11.80          | ~ (v1_funct_1 @ X57))),
% 11.57/11.80      inference('cnf', [status(esa)], [t67_funct_2])).
% 11.57/11.80  thf('182', plain,
% 11.57/11.80      ((~ (v1_funct_1 @ sk_C)
% 11.57/11.80        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 11.57/11.80        | ((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (sk_A)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['180', '181'])).
% 11.57/11.80  thf('183', plain, ((v1_funct_1 @ sk_C)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('184', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('185', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('186', plain,
% 11.57/11.80      (![X12 : $i, X13 : $i, X14 : $i]:
% 11.57/11.80         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 11.57/11.80          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 11.57/11.80      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 11.57/11.80  thf('187', plain,
% 11.57/11.80      (((k1_relset_1 @ sk_A @ sk_A @ sk_C) = (k1_relat_1 @ sk_C))),
% 11.57/11.80      inference('sup-', [status(thm)], ['185', '186'])).
% 11.57/11.80  thf('188', plain, (((k1_relat_1 @ sk_C) = (sk_A))),
% 11.57/11.80      inference('demod', [status(thm)], ['182', '183', '184', '187'])).
% 11.57/11.80  thf(t64_relat_1, axiom,
% 11.57/11.80    (![A:$i]:
% 11.57/11.80     ( ( v1_relat_1 @ A ) =>
% 11.57/11.80       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 11.57/11.80           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 11.57/11.80         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 11.57/11.80  thf('189', plain,
% 11.57/11.80      (![X8 : $i]:
% 11.57/11.80         (((k1_relat_1 @ X8) != (k1_xboole_0))
% 11.57/11.80          | ((X8) = (k1_xboole_0))
% 11.57/11.80          | ~ (v1_relat_1 @ X8))),
% 11.57/11.80      inference('cnf', [status(esa)], [t64_relat_1])).
% 11.57/11.80  thf('190', plain,
% 11.57/11.80      ((((sk_A) != (k1_xboole_0))
% 11.57/11.80        | ~ (v1_relat_1 @ sk_C)
% 11.57/11.80        | ((sk_C) = (k1_xboole_0)))),
% 11.57/11.80      inference('sup-', [status(thm)], ['188', '189'])).
% 11.57/11.80  thf('191', plain,
% 11.57/11.80      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 11.57/11.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 11.57/11.80  thf('192', plain,
% 11.57/11.80      (![X4 : $i, X5 : $i]:
% 11.57/11.80         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 11.57/11.80          | (v1_relat_1 @ X4)
% 11.57/11.80          | ~ (v1_relat_1 @ X5))),
% 11.57/11.80      inference('cnf', [status(esa)], [cc2_relat_1])).
% 11.57/11.80  thf('193', plain,
% 11.57/11.80      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 11.57/11.80      inference('sup-', [status(thm)], ['191', '192'])).
% 11.57/11.80  thf('194', plain,
% 11.57/11.80      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 11.57/11.80      inference('cnf', [status(esa)], [fc6_relat_1])).
% 11.57/11.80  thf('195', plain, ((v1_relat_1 @ sk_C)),
% 11.57/11.80      inference('demod', [status(thm)], ['193', '194'])).
% 11.57/11.80  thf('196', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 11.57/11.80      inference('demod', [status(thm)], ['190', '195'])).
% 11.57/11.80  thf('197', plain, (((sk_A) = (k1_xboole_0))),
% 11.57/11.80      inference('clc', [status(thm)], ['173', '174'])).
% 11.57/11.80  thf('198', plain,
% 11.57/11.80      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C) = (k1_xboole_0)))),
% 11.57/11.80      inference('demod', [status(thm)], ['196', '197'])).
% 11.57/11.80  thf('199', plain, (((sk_C) = (k1_xboole_0))),
% 11.57/11.80      inference('simplify', [status(thm)], ['198'])).
% 11.57/11.80  thf(t4_subset_1, axiom,
% 11.57/11.80    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 11.57/11.80  thf('200', plain,
% 11.57/11.80      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 11.57/11.80      inference('cnf', [status(esa)], [t4_subset_1])).
% 11.57/11.80  thf('201', plain,
% 11.57/11.80      (![X25 : $i, X26 : $i, X27 : $i]:
% 11.57/11.80         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 11.57/11.80          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 11.57/11.80      inference('simplify', [status(thm)], ['156'])).
% 11.57/11.80  thf('202', plain,
% 11.57/11.80      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 11.57/11.80      inference('sup-', [status(thm)], ['200', '201'])).
% 11.57/11.80  thf('203', plain, ($false),
% 11.57/11.80      inference('demod', [status(thm)], ['179', '199', '202'])).
% 11.57/11.80  
% 11.57/11.80  % SZS output end Refutation
% 11.57/11.80  
% 11.57/11.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
