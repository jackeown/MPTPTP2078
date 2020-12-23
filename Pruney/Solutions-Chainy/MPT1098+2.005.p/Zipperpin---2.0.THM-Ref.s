%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8jor2mgguU

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:43 EST 2020

% Result     : Theorem 0.92s
% Output     : Refutation 0.92s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 110 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  522 ( 935 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) @ X13 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf(t13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ A ) ) )).

thf('1',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_finset_1 @ X21 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( v1_finset_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_finset_1 @ X0 )
      | ( v1_finset_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t33_finset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( v1_finset_1 @ A )
          & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
          & ! [D: $i] :
              ~ ( ( v1_finset_1 @ D )
                & ( r1_tarski @ D @ B )
                & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_finset_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t32_finset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( v1_finset_1 @ A )
        & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ~ ( ( v1_finset_1 @ D )
              & ( r1_tarski @ D @ B )
              & ( v1_finset_1 @ E )
              & ( r1_tarski @ E @ C )
              & ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) )).

thf('4',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_finset_1 @ X23 )
      | ( r1_tarski @ X23 @ ( k2_zfmisc_1 @ ( sk_D @ X24 @ X25 @ X23 ) @ ( sk_E @ X24 @ X25 @ X23 ) ) )
      | ~ ( r1_tarski @ X23 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('5',plain,
    ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','16','17'])).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ( v1_finset_1 @ X21 )
      | ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( v1_finset_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('20',plain,
    ( ~ ( v1_finset_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) )
    | ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('28',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X26: $i] :
      ( ~ ( v1_finset_1 @ X26 )
      | ~ ( r1_tarski @ X26 @ sk_B )
      | ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ X26 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) @ X13 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf('32',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ ( k1_relat_1 @ X15 ) )
      | ~ ( r1_tarski @ X16 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('36',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('37',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['31','39'])).

thf('41',plain,(
    ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','40'])).

thf('42',plain,(
    ~ ( v1_finset_1 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['20','41'])).

thf('43',plain,(
    ~ ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_finset_1 @ X23 )
      | ( v1_finset_1 @ ( sk_D @ X24 @ X25 @ X23 ) )
      | ~ ( r1_tarski @ X23 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('46',plain,
    ( ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['43','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8jor2mgguU
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:50:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.92/1.11  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.92/1.11  % Solved by: fo/fo7.sh
% 0.92/1.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.92/1.11  % done 1222 iterations in 0.655s
% 0.92/1.11  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.92/1.11  % SZS output start Refutation
% 0.92/1.11  thf(sk_C_type, type, sk_C: $i).
% 0.92/1.11  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.92/1.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.92/1.11  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.92/1.11  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.92/1.11  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.92/1.11  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.92/1.11  thf(sk_B_type, type, sk_B: $i).
% 0.92/1.11  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.92/1.11  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.92/1.11  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.92/1.11  thf(sk_A_type, type, sk_A: $i).
% 0.92/1.11  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.92/1.11  thf(t193_relat_1, axiom,
% 0.92/1.11    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.92/1.11  thf('0', plain,
% 0.92/1.11      (![X13 : $i, X14 : $i]:
% 0.92/1.11         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14)) @ X13)),
% 0.92/1.11      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.92/1.11  thf(t13_finset_1, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( ( r1_tarski @ A @ B ) & ( v1_finset_1 @ B ) ) => ( v1_finset_1 @ A ) ))).
% 0.92/1.11  thf('1', plain,
% 0.92/1.11      (![X21 : $i, X22 : $i]:
% 0.92/1.11         ((v1_finset_1 @ X21)
% 0.92/1.11          | ~ (r1_tarski @ X21 @ X22)
% 0.92/1.11          | ~ (v1_finset_1 @ X22))),
% 0.92/1.11      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.92/1.11  thf('2', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]:
% 0.92/1.11         (~ (v1_finset_1 @ X0)
% 0.92/1.11          | (v1_finset_1 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['0', '1'])).
% 0.92/1.11  thf(t33_finset_1, conjecture,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.92/1.11          ( ![D:$i]:
% 0.92/1.11            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.92/1.11                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ))).
% 0.92/1.11  thf(zf_stmt_0, negated_conjecture,
% 0.92/1.11    (~( ![A:$i,B:$i,C:$i]:
% 0.92/1.11        ( ~( ( v1_finset_1 @ A ) & 
% 0.92/1.11             ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.92/1.11             ( ![D:$i]:
% 0.92/1.11               ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.92/1.11                    ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ) )),
% 0.92/1.11    inference('cnf.neg', [status(esa)], [t33_finset_1])).
% 0.92/1.11  thf('3', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(t32_finset_1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.92/1.11          ( ![D:$i,E:$i]:
% 0.92/1.11            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.92/1.11                 ( v1_finset_1 @ E ) & ( r1_tarski @ E @ C ) & 
% 0.92/1.11                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) ) ) ))).
% 0.92/1.11  thf('4', plain,
% 0.92/1.11      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.92/1.11         (~ (v1_finset_1 @ X23)
% 0.92/1.11          | (r1_tarski @ X23 @ 
% 0.92/1.11             (k2_zfmisc_1 @ (sk_D @ X24 @ X25 @ X23) @ (sk_E @ X24 @ X25 @ X23)))
% 0.92/1.11          | ~ (r1_tarski @ X23 @ (k2_zfmisc_1 @ X25 @ X24)))),
% 0.92/1.11      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.92/1.11  thf('5', plain,
% 0.92/1.11      (((r1_tarski @ sk_A @ 
% 0.92/1.11         (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.92/1.11          (sk_E @ sk_C @ sk_B @ sk_A)))
% 0.92/1.11        | ~ (v1_finset_1 @ sk_A))),
% 0.92/1.11      inference('sup-', [status(thm)], ['3', '4'])).
% 0.92/1.11  thf('6', plain, ((v1_finset_1 @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('7', plain,
% 0.92/1.11      ((r1_tarski @ sk_A @ 
% 0.92/1.11        (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.92/1.11         (sk_E @ sk_C @ sk_B @ sk_A)))),
% 0.92/1.11      inference('demod', [status(thm)], ['5', '6'])).
% 0.92/1.11  thf(t25_relat_1, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( v1_relat_1 @ A ) =>
% 0.92/1.11       ( ![B:$i]:
% 0.92/1.11         ( ( v1_relat_1 @ B ) =>
% 0.92/1.11           ( ( r1_tarski @ A @ B ) =>
% 0.92/1.11             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.92/1.11               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.92/1.11  thf('8', plain,
% 0.92/1.11      (![X15 : $i, X16 : $i]:
% 0.92/1.11         (~ (v1_relat_1 @ X15)
% 0.92/1.11          | (r1_tarski @ (k1_relat_1 @ X16) @ (k1_relat_1 @ X15))
% 0.92/1.11          | ~ (r1_tarski @ X16 @ X15)
% 0.92/1.11          | ~ (v1_relat_1 @ X16))),
% 0.92/1.11      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.92/1.11  thf('9', plain,
% 0.92/1.11      ((~ (v1_relat_1 @ sk_A)
% 0.92/1.11        | (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 0.92/1.11           (k1_relat_1 @ 
% 0.92/1.11            (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.92/1.11             (sk_E @ sk_C @ sk_B @ sk_A))))
% 0.92/1.11        | ~ (v1_relat_1 @ 
% 0.92/1.11             (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.92/1.11              (sk_E @ sk_C @ sk_B @ sk_A))))),
% 0.92/1.11      inference('sup-', [status(thm)], ['7', '8'])).
% 0.92/1.11  thf('10', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf(t3_subset, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.92/1.11  thf('11', plain,
% 0.92/1.11      (![X6 : $i, X8 : $i]:
% 0.92/1.11         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.92/1.11      inference('cnf', [status(esa)], [t3_subset])).
% 0.92/1.11  thf('12', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.92/1.11  thf(cc2_relat_1, axiom,
% 0.92/1.11    (![A:$i]:
% 0.92/1.11     ( ( v1_relat_1 @ A ) =>
% 0.92/1.11       ( ![B:$i]:
% 0.92/1.11         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.92/1.11  thf('13', plain,
% 0.92/1.11      (![X9 : $i, X10 : $i]:
% 0.92/1.11         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.92/1.11          | (v1_relat_1 @ X9)
% 0.92/1.11          | ~ (v1_relat_1 @ X10))),
% 0.92/1.11      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.92/1.11  thf('14', plain,
% 0.92/1.11      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_A))),
% 0.92/1.11      inference('sup-', [status(thm)], ['12', '13'])).
% 0.92/1.11  thf(fc6_relat_1, axiom,
% 0.92/1.11    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.92/1.11  thf('15', plain,
% 0.92/1.11      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.92/1.11      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.92/1.11  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.92/1.11      inference('demod', [status(thm)], ['14', '15'])).
% 0.92/1.11  thf('17', plain,
% 0.92/1.11      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.92/1.11      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.92/1.11  thf('18', plain,
% 0.92/1.11      ((r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 0.92/1.11        (k1_relat_1 @ 
% 0.92/1.11         (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.92/1.11          (sk_E @ sk_C @ sk_B @ sk_A))))),
% 0.92/1.11      inference('demod', [status(thm)], ['9', '16', '17'])).
% 0.92/1.11  thf('19', plain,
% 0.92/1.11      (![X21 : $i, X22 : $i]:
% 0.92/1.11         ((v1_finset_1 @ X21)
% 0.92/1.11          | ~ (r1_tarski @ X21 @ X22)
% 0.92/1.11          | ~ (v1_finset_1 @ X22))),
% 0.92/1.11      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.92/1.11  thf('20', plain,
% 0.92/1.11      ((~ (v1_finset_1 @ 
% 0.92/1.11           (k1_relat_1 @ 
% 0.92/1.11            (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.92/1.11             (sk_E @ sk_C @ sk_B @ sk_A))))
% 0.92/1.11        | (v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['18', '19'])).
% 0.92/1.11  thf(d10_xboole_0, axiom,
% 0.92/1.11    (![A:$i,B:$i]:
% 0.92/1.11     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.92/1.11  thf('21', plain,
% 0.92/1.11      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.92/1.11      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.92/1.11  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.92/1.11      inference('simplify', [status(thm)], ['21'])).
% 0.92/1.11  thf('23', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['10', '11'])).
% 0.92/1.11  thf(t13_relset_1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i,D:$i]:
% 0.92/1.11     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.92/1.11       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.92/1.11         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.92/1.11  thf('24', plain,
% 0.92/1.11      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.92/1.11         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.92/1.11          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.92/1.11          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X19))))),
% 0.92/1.11      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.92/1.11  thf('25', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))
% 0.92/1.11          | ~ (r1_tarski @ (k1_relat_1 @ sk_A) @ X0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['23', '24'])).
% 0.92/1.11  thf('26', plain,
% 0.92/1.11      ((m1_subset_1 @ sk_A @ 
% 0.92/1.11        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ sk_C)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['22', '25'])).
% 0.92/1.11  thf('27', plain,
% 0.92/1.11      (![X6 : $i, X7 : $i]:
% 0.92/1.11         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.92/1.11      inference('cnf', [status(esa)], [t3_subset])).
% 0.92/1.11  thf('28', plain,
% 0.92/1.11      ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ sk_C))),
% 0.92/1.11      inference('sup-', [status(thm)], ['26', '27'])).
% 0.92/1.11  thf('29', plain,
% 0.92/1.11      (![X26 : $i]:
% 0.92/1.11         (~ (v1_finset_1 @ X26)
% 0.92/1.11          | ~ (r1_tarski @ X26 @ sk_B)
% 0.92/1.11          | ~ (r1_tarski @ sk_A @ (k2_zfmisc_1 @ X26 @ sk_C)))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('30', plain,
% 0.92/1.11      ((~ (r1_tarski @ (k1_relat_1 @ sk_A) @ sk_B)
% 0.92/1.11        | ~ (v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['28', '29'])).
% 0.92/1.11  thf('31', plain,
% 0.92/1.11      (![X13 : $i, X14 : $i]:
% 0.92/1.11         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14)) @ X13)),
% 0.92/1.11      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.92/1.11  thf('32', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('33', plain,
% 0.92/1.11      (![X15 : $i, X16 : $i]:
% 0.92/1.11         (~ (v1_relat_1 @ X15)
% 0.92/1.11          | (r1_tarski @ (k1_relat_1 @ X16) @ (k1_relat_1 @ X15))
% 0.92/1.11          | ~ (r1_tarski @ X16 @ X15)
% 0.92/1.11          | ~ (v1_relat_1 @ X16))),
% 0.92/1.11      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.92/1.11  thf('34', plain,
% 0.92/1.11      ((~ (v1_relat_1 @ sk_A)
% 0.92/1.11        | (r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 0.92/1.11           (k1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))
% 0.92/1.11        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.92/1.11      inference('sup-', [status(thm)], ['32', '33'])).
% 0.92/1.11  thf('35', plain, ((v1_relat_1 @ sk_A)),
% 0.92/1.11      inference('demod', [status(thm)], ['14', '15'])).
% 0.92/1.11  thf('36', plain,
% 0.92/1.11      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.92/1.11      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.92/1.11  thf('37', plain,
% 0.92/1.11      ((r1_tarski @ (k1_relat_1 @ sk_A) @ 
% 0.92/1.11        (k1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.92/1.11      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.92/1.11  thf(t1_xboole_1, axiom,
% 0.92/1.11    (![A:$i,B:$i,C:$i]:
% 0.92/1.11     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.92/1.11       ( r1_tarski @ A @ C ) ))).
% 0.92/1.11  thf('38', plain,
% 0.92/1.11      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.92/1.11         (~ (r1_tarski @ X3 @ X4)
% 0.92/1.11          | ~ (r1_tarski @ X4 @ X5)
% 0.92/1.11          | (r1_tarski @ X3 @ X5))),
% 0.92/1.11      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.92/1.11  thf('39', plain,
% 0.92/1.11      (![X0 : $i]:
% 0.92/1.11         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 0.92/1.11          | ~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) @ X0))),
% 0.92/1.11      inference('sup-', [status(thm)], ['37', '38'])).
% 0.92/1.11  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ sk_B)),
% 0.92/1.11      inference('sup-', [status(thm)], ['31', '39'])).
% 0.92/1.11  thf('41', plain, (~ (v1_finset_1 @ (k1_relat_1 @ sk_A))),
% 0.92/1.11      inference('demod', [status(thm)], ['30', '40'])).
% 0.92/1.11  thf('42', plain,
% 0.92/1.11      (~ (v1_finset_1 @ 
% 0.92/1.11          (k1_relat_1 @ 
% 0.92/1.11           (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.92/1.11            (sk_E @ sk_C @ sk_B @ sk_A))))),
% 0.92/1.11      inference('clc', [status(thm)], ['20', '41'])).
% 0.92/1.11  thf('43', plain, (~ (v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A))),
% 0.92/1.11      inference('sup-', [status(thm)], ['2', '42'])).
% 0.92/1.11  thf('44', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('45', plain,
% 0.92/1.11      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.92/1.11         (~ (v1_finset_1 @ X23)
% 0.92/1.11          | (v1_finset_1 @ (sk_D @ X24 @ X25 @ X23))
% 0.92/1.11          | ~ (r1_tarski @ X23 @ (k2_zfmisc_1 @ X25 @ X24)))),
% 0.92/1.11      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.92/1.11  thf('46', plain,
% 0.92/1.11      (((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A)) | ~ (v1_finset_1 @ sk_A))),
% 0.92/1.11      inference('sup-', [status(thm)], ['44', '45'])).
% 0.92/1.11  thf('47', plain, ((v1_finset_1 @ sk_A)),
% 0.92/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.92/1.11  thf('48', plain, ((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A))),
% 0.92/1.11      inference('demod', [status(thm)], ['46', '47'])).
% 0.92/1.11  thf('49', plain, ($false), inference('demod', [status(thm)], ['43', '48'])).
% 0.92/1.11  
% 0.92/1.11  % SZS output end Refutation
% 0.92/1.11  
% 0.92/1.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
