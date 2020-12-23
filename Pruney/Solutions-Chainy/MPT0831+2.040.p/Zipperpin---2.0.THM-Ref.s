%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jOwPakKCeB

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:25 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 123 expanded)
%              Number of leaves         :   27 (  48 expanded)
%              Depth                    :   17
%              Number of atoms          :  471 (1009 expanded)
%              Number of equality atoms :   12 (  13 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t34_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relset_1])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ ( k5_relset_1 @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k5_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k7_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_B @ sk_A @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ ( k7_relat_1 @ sk_D @ sk_C ) @ sk_D ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('23',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('25',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('27',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['25','26'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['16','29'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X24 ) @ X25 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X26 )
      | ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','34'])).

thf('36',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v4_relat_1 @ sk_D @ sk_C ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X9: $i,X10: $i] :
      ( ( X9
        = ( k7_relat_1 @ X9 @ X10 ) )
      | ~ ( v4_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('41',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_C ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D ) ),
    inference(demod,[status(thm)],['4','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('44',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('45',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['42','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.jOwPakKCeB
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.53  % Solved by: fo/fo7.sh
% 0.22/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.53  % done 88 iterations in 0.078s
% 0.22/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.53  % SZS output start Refutation
% 0.22/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.53  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.53  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.22/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.53  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.53  thf(t34_relset_1, conjecture,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.53       ( ( r1_tarski @ B @ C ) =>
% 0.22/0.53         ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ))).
% 0.22/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.22/0.53          ( ( r1_tarski @ B @ C ) =>
% 0.22/0.53            ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )),
% 0.22/0.53    inference('cnf.neg', [status(esa)], [t34_relset_1])).
% 0.22/0.53  thf('0', plain,
% 0.22/0.53      (~ (r2_relset_1 @ sk_B @ sk_A @ 
% 0.22/0.53          (k5_relset_1 @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_D)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('1', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_k5_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.22/0.53  thf('2', plain,
% 0.22/0.53      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.22/0.53          | ((k5_relset_1 @ X17 @ X18 @ X16 @ X19) = (k7_relat_1 @ X16 @ X19)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.22/0.53  thf('3', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((k5_relset_1 @ sk_B @ sk_A @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.53  thf('4', plain,
% 0.22/0.53      (~ (r2_relset_1 @ sk_B @ sk_A @ (k7_relat_1 @ sk_D @ sk_C) @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.53  thf('5', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(cc2_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.53  thf('6', plain,
% 0.22/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         ((v5_relat_1 @ X13 @ X15)
% 0.22/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.53  thf('7', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.22/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.53  thf(d19_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.53  thf('8', plain,
% 0.22/0.53      (![X5 : $i, X6 : $i]:
% 0.22/0.53         (~ (v5_relat_1 @ X5 @ X6)
% 0.22/0.53          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.22/0.53          | ~ (v1_relat_1 @ X5))),
% 0.22/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.53  thf('9', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.22/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.53  thf('10', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(cc2_relat_1, axiom,
% 0.22/0.53    (![A:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ A ) =>
% 0.22/0.53       ( ![B:$i]:
% 0.22/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.53  thf('11', plain,
% 0.22/0.53      (![X3 : $i, X4 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.22/0.53          | (v1_relat_1 @ X3)
% 0.22/0.53          | ~ (v1_relat_1 @ X4))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.53  thf('12', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.22/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.53  thf(fc6_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.53  thf('13', plain,
% 0.22/0.53      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.22/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.53  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.53  thf('15', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.22/0.53      inference('demod', [status(thm)], ['9', '14'])).
% 0.22/0.53  thf('16', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('17', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf('18', plain,
% 0.22/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         ((v4_relat_1 @ X13 @ X14)
% 0.22/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.53  thf('19', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.22/0.53      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.53  thf(t209_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.53  thf('20', plain,
% 0.22/0.53      (![X9 : $i, X10 : $i]:
% 0.22/0.53         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.22/0.53          | ~ (v4_relat_1 @ X9 @ X10)
% 0.22/0.53          | ~ (v1_relat_1 @ X9))),
% 0.22/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.53  thf('21', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_B)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.53  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.53  thf('23', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_B))),
% 0.22/0.53      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.53  thf(t87_relat_1, axiom,
% 0.22/0.53    (![A:$i,B:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ B ) =>
% 0.22/0.53       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.22/0.53  thf('24', plain,
% 0.22/0.53      (![X11 : $i, X12 : $i]:
% 0.22/0.53         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X11 @ X12)) @ X12)
% 0.22/0.53          | ~ (v1_relat_1 @ X11))),
% 0.22/0.53      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.22/0.53  thf('25', plain,
% 0.22/0.53      (((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B) | ~ (v1_relat_1 @ sk_D))),
% 0.22/0.53      inference('sup+', [status(thm)], ['23', '24'])).
% 0.22/0.53  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.53  thf('27', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.22/0.53      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.53  thf(t1_xboole_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.53       ( r1_tarski @ A @ C ) ))).
% 0.22/0.53  thf('28', plain,
% 0.22/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.22/0.53          | ~ (r1_tarski @ X1 @ X2)
% 0.22/0.53          | (r1_tarski @ X0 @ X2))),
% 0.22/0.53      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.53  thf('29', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((r1_tarski @ (k1_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.53  thf('30', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_C)),
% 0.22/0.53      inference('sup-', [status(thm)], ['16', '29'])).
% 0.22/0.53  thf(t11_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i]:
% 0.22/0.53     ( ( v1_relat_1 @ C ) =>
% 0.22/0.53       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.22/0.53           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.22/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.22/0.53  thf('31', plain,
% 0.22/0.53      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.22/0.53         (~ (r1_tarski @ (k1_relat_1 @ X24) @ X25)
% 0.22/0.53          | ~ (r1_tarski @ (k2_relat_1 @ X24) @ X26)
% 0.22/0.53          | (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.22/0.53          | ~ (v1_relat_1 @ X24))),
% 0.22/0.53      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.22/0.53  thf('32', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         (~ (v1_relat_1 @ sk_D)
% 0.22/0.53          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))
% 0.22/0.53          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.22/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.53  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.53  thf('34', plain,
% 0.22/0.53      (![X0 : $i]:
% 0.22/0.53         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ X0)))
% 0.22/0.53          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.22/0.53      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.53  thf('35', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_A)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['15', '34'])).
% 0.22/0.53  thf('36', plain,
% 0.22/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.53         ((v4_relat_1 @ X13 @ X14)
% 0.22/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.22/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.53  thf('37', plain, ((v4_relat_1 @ sk_D @ sk_C)),
% 0.22/0.53      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.53  thf('38', plain,
% 0.22/0.53      (![X9 : $i, X10 : $i]:
% 0.22/0.53         (((X9) = (k7_relat_1 @ X9 @ X10))
% 0.22/0.53          | ~ (v4_relat_1 @ X9 @ X10)
% 0.22/0.53          | ~ (v1_relat_1 @ X9))),
% 0.22/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.53  thf('39', plain,
% 0.22/0.53      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_C)))),
% 0.22/0.53      inference('sup-', [status(thm)], ['37', '38'])).
% 0.22/0.53  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.22/0.53  thf('41', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_C))),
% 0.22/0.53      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.53  thf('42', plain, (~ (r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D)),
% 0.22/0.53      inference('demod', [status(thm)], ['4', '41'])).
% 0.22/0.53  thf('43', plain,
% 0.22/0.53      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.22/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.53  thf(redefinition_r2_relset_1, axiom,
% 0.22/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.53     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.53       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.22/0.53  thf('44', plain,
% 0.22/0.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.53         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.22/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.22/0.53          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 0.22/0.53          | ((X20) != (X23)))),
% 0.22/0.53      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.22/0.53  thf('45', plain,
% 0.22/0.53      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.22/0.53         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.22/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.22/0.53      inference('simplify', [status(thm)], ['44'])).
% 0.22/0.53  thf('46', plain, ((r2_relset_1 @ sk_B @ sk_A @ sk_D @ sk_D)),
% 0.22/0.53      inference('sup-', [status(thm)], ['43', '45'])).
% 0.22/0.53  thf('47', plain, ($false), inference('demod', [status(thm)], ['42', '46'])).
% 0.22/0.53  
% 0.22/0.53  % SZS output end Refutation
% 0.22/0.53  
% 0.41/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
