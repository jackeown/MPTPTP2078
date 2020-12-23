%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wui7ANRlUJ

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:44 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   55 (  74 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   11
%              Number of atoms          :  347 ( 557 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t13_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
       => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
         => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) @ X17 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('4',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( r1_tarski @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['6','11','12'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['1','15'])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X8 @ X6 ) @ ( k2_zfmisc_1 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ ( k2_relat_1 @ sk_D ) ) @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X6 @ X8 ) @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X18: $i] :
      ( ( r1_tarski @ X18 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X18 ) @ ( k2_relat_1 @ X18 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_D ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['9','10'])).

thf('27',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D @ X0 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ ( k2_relat_1 @ sk_D ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    $false ),
    inference(demod,[status(thm)],['0','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Wui7ANRlUJ
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:10 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 154 iterations in 0.086s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.36/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.36/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.54  thf(t13_relset_1, conjecture,
% 0.36/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.36/0.54       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.36/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.54        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.36/0.54          ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.36/0.54            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t13_relset_1])).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t194_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X16 : $i, X17 : $i]:
% 0.36/0.54         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X16 @ X17)) @ X17)),
% 0.36/0.54      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(t3_subset, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (![X9 : $i, X10 : $i]:
% 0.36/0.54         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.54  thf('4', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.54  thf(t25_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( v1_relat_1 @ B ) =>
% 0.36/0.54           ( ( r1_tarski @ A @ B ) =>
% 0.36/0.54             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.36/0.54               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X19 : $i, X20 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X19)
% 0.36/0.54          | (r1_tarski @ (k2_relat_1 @ X20) @ (k2_relat_1 @ X19))
% 0.36/0.54          | ~ (r1_tarski @ X20 @ X19)
% 0.36/0.54          | ~ (v1_relat_1 @ X20))),
% 0.36/0.54      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ sk_D)
% 0.36/0.54        | (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.36/0.54           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.36/0.54        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(cc2_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( ![B:$i]:
% 0.36/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X12 : $i, X13 : $i]:
% 0.36/0.54         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.36/0.54          | (v1_relat_1 @ X12)
% 0.36/0.54          | ~ (v1_relat_1 @ X13))),
% 0.36/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D))),
% 0.36/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.54  thf(fc6_relat_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.36/0.54  thf('10', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.54  thf('11', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf('12', plain,
% 0.36/0.54      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.36/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      ((r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 0.36/0.54        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.36/0.54      inference('demod', [status(thm)], ['6', '11', '12'])).
% 0.36/0.54  thf(t1_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.54       ( r1_tarski @ A @ C ) ))).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         (~ (r1_tarski @ X3 @ X4)
% 0.36/0.54          | ~ (r1_tarski @ X4 @ X5)
% 0.36/0.54          | (r1_tarski @ X3 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0)
% 0.36/0.54          | ~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.36/0.54  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.36/0.54      inference('sup-', [status(thm)], ['1', '15'])).
% 0.36/0.54  thf(t118_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i,C:$i]:
% 0.36/0.54     ( ( r1_tarski @ A @ B ) =>
% 0.36/0.54       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.36/0.54         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.54         (~ (r1_tarski @ X6 @ X7)
% 0.36/0.54          | (r1_tarski @ (k2_zfmisc_1 @ X8 @ X6) @ (k2_zfmisc_1 @ X8 @ X7)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.36/0.54  thf('18', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (r1_tarski @ (k2_zfmisc_1 @ X0 @ (k2_relat_1 @ sk_D)) @ 
% 0.36/0.54          (k2_zfmisc_1 @ X0 @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_B)),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf('20', plain,
% 0.36/0.54      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.36/0.54         (~ (r1_tarski @ X6 @ X7)
% 0.36/0.54          | (r1_tarski @ (k2_zfmisc_1 @ X6 @ X8) @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.36/0.54      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.36/0.54  thf('21', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         (r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ 
% 0.36/0.54          (k2_zfmisc_1 @ sk_B @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.54  thf(t21_relat_1, axiom,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( v1_relat_1 @ A ) =>
% 0.36/0.54       ( r1_tarski @
% 0.36/0.54         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.36/0.54  thf('22', plain,
% 0.36/0.54      (![X18 : $i]:
% 0.36/0.54         ((r1_tarski @ X18 @ 
% 0.36/0.54           (k2_zfmisc_1 @ (k1_relat_1 @ X18) @ (k2_relat_1 @ X18)))
% 0.36/0.54          | ~ (v1_relat_1 @ X18))),
% 0.36/0.54      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.36/0.54  thf('23', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         (~ (r1_tarski @ X3 @ X4)
% 0.36/0.54          | ~ (r1_tarski @ X4 @ X5)
% 0.36/0.54          | (r1_tarski @ X3 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.54  thf('24', plain,
% 0.36/0.54      (![X0 : $i, X1 : $i]:
% 0.36/0.54         (~ (v1_relat_1 @ X0)
% 0.36/0.54          | (r1_tarski @ X0 @ X1)
% 0.36/0.54          | ~ (r1_tarski @ 
% 0.36/0.54               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)) @ X1))),
% 0.36/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.36/0.54  thf('25', plain,
% 0.36/0.54      (((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_D)))
% 0.36/0.54        | ~ (v1_relat_1 @ sk_D))),
% 0.36/0.54      inference('sup-', [status(thm)], ['21', '24'])).
% 0.36/0.54  thf('26', plain, ((v1_relat_1 @ sk_D)),
% 0.36/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.36/0.54  thf('27', plain,
% 0.36/0.54      ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_D)))),
% 0.36/0.54      inference('demod', [status(thm)], ['25', '26'])).
% 0.36/0.54  thf('28', plain,
% 0.36/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.54         (~ (r1_tarski @ X3 @ X4)
% 0.36/0.54          | ~ (r1_tarski @ X4 @ X5)
% 0.36/0.54          | (r1_tarski @ X3 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.54  thf('29', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((r1_tarski @ sk_D @ X0)
% 0.36/0.54          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_B @ (k2_relat_1 @ sk_D)) @ X0))),
% 0.36/0.54      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.54  thf('30', plain, ((r1_tarski @ sk_D @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.36/0.54      inference('sup-', [status(thm)], ['18', '29'])).
% 0.36/0.54  thf('31', plain,
% 0.36/0.54      (![X9 : $i, X11 : $i]:
% 0.36/0.54         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.36/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.36/0.54  thf('32', plain,
% 0.36/0.54      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.36/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.36/0.54  thf('33', plain, ($false), inference('demod', [status(thm)], ['0', '32'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
