%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JeBqs8HpQ3

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:43 EST 2020

% Result     : Theorem 0.62s
% Output     : Refutation 0.62s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 128 expanded)
%              Number of leaves         :   25 (  49 expanded)
%              Depth                    :   12
%              Number of atoms          :  486 (1056 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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

thf('0',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('2',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v5_relat_1 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('4',plain,(
    v5_relat_1 @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v5_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k2_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ sk_C ),
    inference(demod,[status(thm)],['6','9'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ X24 )
      | ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('17',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X30: $i] :
      ( ~ ( v1_finset_1 @ X30 )
      | ~ ( r1_tarski @ X30 @ sk_B )
      | ~ ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ X30 @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ sk_B )
    | ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('23',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('24',plain,(
    v4_relat_1 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('25',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_finset_1 @ X27 )
      | ( r1_tarski @ X27 @ ( k2_zfmisc_1 @ ( sk_D @ X28 @ X29 @ X27 ) @ ( sk_E @ X28 @ X29 @ X27 ) ) )
      | ~ ( r1_tarski @ X27 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('32',plain,
    ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_E @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('38',plain,(
    v4_relat_1 @ sk_A @ ( sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_A ),
    inference('sup-',[status(thm)],['7','8'])).

thf('42',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf(t13_finset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( v1_finset_1 @ B ) )
     => ( v1_finset_1 @ A ) ) )).

thf('43',plain,(
    ! [X25: $i,X26: $i] :
      ( ( v1_finset_1 @ X25 )
      | ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( v1_finset_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t13_finset_1])).

thf('44',plain,
    ( ~ ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ( v1_finset_1 @ ( k1_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_finset_1 @ X27 )
      | ( v1_finset_1 @ ( sk_D @ X28 @ X29 @ X27 ) )
      | ~ ( r1_tarski @ X27 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t32_finset_1])).

thf('47',plain,
    ( ( v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_finset_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_finset_1 @ ( sk_D @ sk_C @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    v1_finset_1 @ ( k1_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['44','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['29','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JeBqs8HpQ3
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.62/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.62/0.83  % Solved by: fo/fo7.sh
% 0.62/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.62/0.83  % done 686 iterations in 0.371s
% 0.62/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.62/0.83  % SZS output start Refutation
% 0.62/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.62/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.62/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.62/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.62/0.83  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.62/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.62/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.62/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.62/0.83  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.62/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.62/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.62/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.62/0.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.62/0.83  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.62/0.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.62/0.83  thf(t33_finset_1, conjecture,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.62/0.83          ( ![D:$i]:
% 0.62/0.83            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.62/0.83                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ))).
% 0.62/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.62/0.83    (~( ![A:$i,B:$i,C:$i]:
% 0.62/0.83        ( ~( ( v1_finset_1 @ A ) & 
% 0.62/0.83             ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.62/0.83             ( ![D:$i]:
% 0.62/0.83               ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.62/0.83                    ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ C ) ) ) ) ) ) ) )),
% 0.62/0.83    inference('cnf.neg', [status(esa)], [t33_finset_1])).
% 0.62/0.83  thf('0', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf(t3_subset, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.62/0.83  thf('1', plain,
% 0.62/0.83      (![X3 : $i, X5 : $i]:
% 0.62/0.83         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.62/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.62/0.83  thf('2', plain,
% 0.62/0.83      ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['0', '1'])).
% 0.62/0.83  thf(cc2_relset_1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.83       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.62/0.83  thf('3', plain,
% 0.62/0.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.62/0.83         ((v5_relat_1 @ X19 @ X21)
% 0.62/0.83          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.62/0.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.62/0.83  thf('4', plain, ((v5_relat_1 @ sk_A @ sk_C)),
% 0.62/0.83      inference('sup-', [status(thm)], ['2', '3'])).
% 0.62/0.83  thf(d19_relat_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( v1_relat_1 @ B ) =>
% 0.62/0.83       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.62/0.83  thf('5', plain,
% 0.62/0.83      (![X8 : $i, X9 : $i]:
% 0.62/0.83         (~ (v5_relat_1 @ X8 @ X9)
% 0.62/0.83          | (r1_tarski @ (k2_relat_1 @ X8) @ X9)
% 0.62/0.83          | ~ (v1_relat_1 @ X8))),
% 0.62/0.83      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.62/0.83  thf('6', plain,
% 0.62/0.83      ((~ (v1_relat_1 @ sk_A) | (r1_tarski @ (k2_relat_1 @ sk_A) @ sk_C))),
% 0.62/0.83      inference('sup-', [status(thm)], ['4', '5'])).
% 0.62/0.83  thf('7', plain,
% 0.62/0.83      ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['0', '1'])).
% 0.62/0.83  thf(cc1_relset_1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.62/0.83       ( v1_relat_1 @ C ) ))).
% 0.62/0.83  thf('8', plain,
% 0.62/0.83      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.62/0.83         ((v1_relat_1 @ X16)
% 0.62/0.83          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.62/0.83      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.62/0.83  thf('9', plain, ((v1_relat_1 @ sk_A)),
% 0.62/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.62/0.83  thf('10', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ sk_C)),
% 0.62/0.83      inference('demod', [status(thm)], ['6', '9'])).
% 0.62/0.83  thf(d10_xboole_0, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.62/0.83  thf('11', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.62/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.62/0.83  thf('12', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.62/0.83      inference('simplify', [status(thm)], ['11'])).
% 0.62/0.83  thf(t11_relset_1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ( v1_relat_1 @ C ) =>
% 0.62/0.83       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.62/0.83           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.62/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.62/0.83  thf('13', plain,
% 0.62/0.83      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.62/0.83         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.62/0.83          | ~ (r1_tarski @ (k2_relat_1 @ X22) @ X24)
% 0.62/0.83          | (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.62/0.83          | ~ (v1_relat_1 @ X22))),
% 0.62/0.83      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.62/0.83  thf('14', plain,
% 0.62/0.83      (![X0 : $i, X1 : $i]:
% 0.62/0.83         (~ (v1_relat_1 @ X0)
% 0.62/0.83          | (m1_subset_1 @ X0 @ 
% 0.62/0.83             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.62/0.83          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.62/0.83      inference('sup-', [status(thm)], ['12', '13'])).
% 0.62/0.83  thf('15', plain,
% 0.62/0.83      (((m1_subset_1 @ sk_A @ 
% 0.62/0.83         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ sk_C)))
% 0.62/0.83        | ~ (v1_relat_1 @ sk_A))),
% 0.62/0.83      inference('sup-', [status(thm)], ['10', '14'])).
% 0.62/0.83  thf('16', plain, ((v1_relat_1 @ sk_A)),
% 0.62/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.62/0.83  thf('17', plain,
% 0.62/0.83      ((m1_subset_1 @ sk_A @ 
% 0.62/0.83        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ sk_C)))),
% 0.62/0.83      inference('demod', [status(thm)], ['15', '16'])).
% 0.62/0.83  thf('18', plain,
% 0.62/0.83      (![X3 : $i, X4 : $i]:
% 0.62/0.83         ((r1_tarski @ X3 @ X4) | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.62/0.83  thf('19', plain,
% 0.62/0.83      ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ sk_C))),
% 0.62/0.83      inference('sup-', [status(thm)], ['17', '18'])).
% 0.62/0.83  thf('20', plain,
% 0.62/0.83      (![X30 : $i]:
% 0.62/0.83         (~ (v1_finset_1 @ X30)
% 0.62/0.83          | ~ (r1_tarski @ X30 @ sk_B)
% 0.62/0.83          | ~ (r1_tarski @ sk_A @ (k2_zfmisc_1 @ X30 @ sk_C)))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf('21', plain,
% 0.62/0.83      ((~ (r1_tarski @ (k1_relat_1 @ sk_A) @ sk_B)
% 0.62/0.83        | ~ (v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['19', '20'])).
% 0.62/0.83  thf('22', plain,
% 0.62/0.83      ((m1_subset_1 @ sk_A @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['0', '1'])).
% 0.62/0.83  thf('23', plain,
% 0.62/0.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.62/0.83         ((v4_relat_1 @ X19 @ X20)
% 0.62/0.83          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.62/0.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.62/0.83  thf('24', plain, ((v4_relat_1 @ sk_A @ sk_B)),
% 0.62/0.83      inference('sup-', [status(thm)], ['22', '23'])).
% 0.62/0.83  thf(d18_relat_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( v1_relat_1 @ B ) =>
% 0.62/0.83       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.62/0.83  thf('25', plain,
% 0.62/0.83      (![X6 : $i, X7 : $i]:
% 0.62/0.83         (~ (v4_relat_1 @ X6 @ X7)
% 0.62/0.83          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.62/0.83          | ~ (v1_relat_1 @ X6))),
% 0.62/0.83      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.62/0.83  thf('26', plain,
% 0.62/0.83      ((~ (v1_relat_1 @ sk_A) | (r1_tarski @ (k1_relat_1 @ sk_A) @ sk_B))),
% 0.62/0.83      inference('sup-', [status(thm)], ['24', '25'])).
% 0.62/0.83  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.62/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.62/0.83  thf('28', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ sk_B)),
% 0.62/0.83      inference('demod', [status(thm)], ['26', '27'])).
% 0.62/0.83  thf('29', plain, (~ (v1_finset_1 @ (k1_relat_1 @ sk_A))),
% 0.62/0.83      inference('demod', [status(thm)], ['21', '28'])).
% 0.62/0.83  thf('30', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf(t32_finset_1, axiom,
% 0.62/0.83    (![A:$i,B:$i,C:$i]:
% 0.62/0.83     ( ~( ( v1_finset_1 @ A ) & ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.62/0.83          ( ![D:$i,E:$i]:
% 0.62/0.83            ( ~( ( v1_finset_1 @ D ) & ( r1_tarski @ D @ B ) & 
% 0.62/0.83                 ( v1_finset_1 @ E ) & ( r1_tarski @ E @ C ) & 
% 0.62/0.83                 ( r1_tarski @ A @ ( k2_zfmisc_1 @ D @ E ) ) ) ) ) ) ))).
% 0.62/0.83  thf('31', plain,
% 0.62/0.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.62/0.83         (~ (v1_finset_1 @ X27)
% 0.62/0.83          | (r1_tarski @ X27 @ 
% 0.62/0.83             (k2_zfmisc_1 @ (sk_D @ X28 @ X29 @ X27) @ (sk_E @ X28 @ X29 @ X27)))
% 0.62/0.83          | ~ (r1_tarski @ X27 @ (k2_zfmisc_1 @ X29 @ X28)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.62/0.83  thf('32', plain,
% 0.62/0.83      (((r1_tarski @ sk_A @ 
% 0.62/0.83         (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.62/0.83          (sk_E @ sk_C @ sk_B @ sk_A)))
% 0.62/0.83        | ~ (v1_finset_1 @ sk_A))),
% 0.62/0.83      inference('sup-', [status(thm)], ['30', '31'])).
% 0.62/0.83  thf('33', plain, ((v1_finset_1 @ sk_A)),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf('34', plain,
% 0.62/0.83      ((r1_tarski @ sk_A @ 
% 0.62/0.83        (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.62/0.83         (sk_E @ sk_C @ sk_B @ sk_A)))),
% 0.62/0.83      inference('demod', [status(thm)], ['32', '33'])).
% 0.62/0.83  thf('35', plain,
% 0.62/0.83      (![X3 : $i, X5 : $i]:
% 0.62/0.83         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.62/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.62/0.83  thf('36', plain,
% 0.62/0.83      ((m1_subset_1 @ sk_A @ 
% 0.62/0.83        (k1_zfmisc_1 @ 
% 0.62/0.83         (k2_zfmisc_1 @ (sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.62/0.83          (sk_E @ sk_C @ sk_B @ sk_A))))),
% 0.62/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.62/0.83  thf('37', plain,
% 0.62/0.83      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.62/0.83         ((v4_relat_1 @ X19 @ X20)
% 0.62/0.83          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.62/0.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.62/0.83  thf('38', plain, ((v4_relat_1 @ sk_A @ (sk_D @ sk_C @ sk_B @ sk_A))),
% 0.62/0.83      inference('sup-', [status(thm)], ['36', '37'])).
% 0.62/0.83  thf('39', plain,
% 0.62/0.83      (![X6 : $i, X7 : $i]:
% 0.62/0.83         (~ (v4_relat_1 @ X6 @ X7)
% 0.62/0.83          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.62/0.83          | ~ (v1_relat_1 @ X6))),
% 0.62/0.83      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.62/0.83  thf('40', plain,
% 0.62/0.83      ((~ (v1_relat_1 @ sk_A)
% 0.62/0.83        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['38', '39'])).
% 0.62/0.83  thf('41', plain, ((v1_relat_1 @ sk_A)),
% 0.62/0.83      inference('sup-', [status(thm)], ['7', '8'])).
% 0.62/0.83  thf('42', plain,
% 0.62/0.83      ((r1_tarski @ (k1_relat_1 @ sk_A) @ (sk_D @ sk_C @ sk_B @ sk_A))),
% 0.62/0.83      inference('demod', [status(thm)], ['40', '41'])).
% 0.62/0.83  thf(t13_finset_1, axiom,
% 0.62/0.83    (![A:$i,B:$i]:
% 0.62/0.83     ( ( ( r1_tarski @ A @ B ) & ( v1_finset_1 @ B ) ) => ( v1_finset_1 @ A ) ))).
% 0.62/0.83  thf('43', plain,
% 0.62/0.83      (![X25 : $i, X26 : $i]:
% 0.62/0.83         ((v1_finset_1 @ X25)
% 0.62/0.83          | ~ (r1_tarski @ X25 @ X26)
% 0.62/0.83          | ~ (v1_finset_1 @ X26))),
% 0.62/0.83      inference('cnf', [status(esa)], [t13_finset_1])).
% 0.62/0.83  thf('44', plain,
% 0.62/0.83      ((~ (v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A))
% 0.62/0.83        | (v1_finset_1 @ (k1_relat_1 @ sk_A)))),
% 0.62/0.83      inference('sup-', [status(thm)], ['42', '43'])).
% 0.62/0.83  thf('45', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf('46', plain,
% 0.62/0.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.62/0.83         (~ (v1_finset_1 @ X27)
% 0.62/0.83          | (v1_finset_1 @ (sk_D @ X28 @ X29 @ X27))
% 0.62/0.83          | ~ (r1_tarski @ X27 @ (k2_zfmisc_1 @ X29 @ X28)))),
% 0.62/0.83      inference('cnf', [status(esa)], [t32_finset_1])).
% 0.62/0.83  thf('47', plain,
% 0.62/0.83      (((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A)) | ~ (v1_finset_1 @ sk_A))),
% 0.62/0.83      inference('sup-', [status(thm)], ['45', '46'])).
% 0.62/0.83  thf('48', plain, ((v1_finset_1 @ sk_A)),
% 0.62/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.62/0.83  thf('49', plain, ((v1_finset_1 @ (sk_D @ sk_C @ sk_B @ sk_A))),
% 0.62/0.83      inference('demod', [status(thm)], ['47', '48'])).
% 0.62/0.83  thf('50', plain, ((v1_finset_1 @ (k1_relat_1 @ sk_A))),
% 0.62/0.83      inference('demod', [status(thm)], ['44', '49'])).
% 0.62/0.83  thf('51', plain, ($false), inference('demod', [status(thm)], ['29', '50'])).
% 0.62/0.83  
% 0.62/0.83  % SZS output end Refutation
% 0.62/0.83  
% 0.66/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
