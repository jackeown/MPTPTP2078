%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sdcjnlBojh

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 282 expanded)
%              Number of leaves         :   20 (  93 expanded)
%              Depth                    :   17
%              Number of atoms          :  515 (2633 expanded)
%              Number of equality atoms :   31 ( 179 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ ( k2_xboole_0 @ X10 @ X11 ) )
      | ~ ( r1_xboole_0 @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_tarski @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t64_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( ( k3_subset_1 @ A @ B )
              = ( k3_subset_1 @ A @ C ) )
           => ( B = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( ( ( k3_subset_1 @ A @ B )
                = ( k3_subset_1 @ A @ C ) )
             => ( B = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X13 @ X12 ) @ ( k3_subset_1 @ X13 @ X14 ) )
      | ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ X0 ) @ ( k3_subset_1 @ sk_A @ sk_B ) )
      | ( r1_tarski @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ ( sk_D @ X2 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( sk_D @ sk_B @ sk_C @ sk_C ) @ sk_C )
    | ( sk_C
      = ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('22',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X13 @ X12 ) @ ( k3_subset_1 @ X13 @ X14 ) )
      | ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ sk_B ) @ ( k3_subset_1 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k3_xboole_0 @ sk_C @ X0 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ sk_C @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r1_tarski @ ( sk_D @ sk_B @ sk_C @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('34',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_C @ sk_B ) )
    | ( sk_B
      = ( k3_xboole_0 @ sk_C @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( r1_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('36',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['27','28'])).

thf('37',plain,
    ( ( sk_B
      = ( k3_xboole_0 @ sk_C @ sk_B ) )
    | ( sk_B
      = ( k3_xboole_0 @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( r1_tarski @ ( sk_D @ sk_B @ sk_C @ sk_C ) @ sk_C )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['19','38'])).

thf('40',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( sk_D @ sk_B @ sk_C @ sk_C ) @ sk_C ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ~ ( r1_tarski @ ( sk_D @ X2 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('43',plain,
    ( ( sk_C
      = ( k3_xboole_0 @ sk_C @ sk_B ) )
    | ~ ( r1_tarski @ sk_C @ sk_B )
    | ~ ( r1_tarski @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_B
    = ( k3_xboole_0 @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['37'])).

thf('45',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['13','14'])).

thf('46',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','6'])).

thf('47',plain,(
    sk_C = sk_B ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    sk_B != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sdcjnlBojh
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:42:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.53  % Solved by: fo/fo7.sh
% 0.21/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.53  % done 97 iterations in 0.067s
% 0.21/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.53  % SZS output start Refutation
% 0.21/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.53  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.21/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.53  thf('0', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.21/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.53  thf(t46_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.53  thf('1', plain,
% 0.21/0.53      (![X6 : $i, X7 : $i]:
% 0.21/0.53         ((k4_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (k1_xboole_0))),
% 0.21/0.53      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.21/0.53  thf(t37_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('2', plain,
% 0.21/0.53      (![X3 : $i, X4 : $i]:
% 0.21/0.53         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t37_xboole_1])).
% 0.21/0.53  thf('3', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.53          | (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.53  thf('4', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.53      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.53  thf(t73_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.21/0.53       ( r1_tarski @ A @ B ) ))).
% 0.21/0.53  thf('5', plain,
% 0.21/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.53         ((r1_tarski @ X9 @ X10)
% 0.21/0.53          | ~ (r1_tarski @ X9 @ (k2_xboole_0 @ X10 @ X11))
% 0.21/0.53          | ~ (r1_xboole_0 @ X9 @ X11))),
% 0.21/0.53      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.21/0.53  thf('6', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]: (~ (r1_xboole_0 @ X1 @ X0) | (r1_tarski @ X1 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.53  thf('7', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.53  thf(t64_subset_1, conjecture,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53           ( ( ( k3_subset_1 @ A @ B ) = ( k3_subset_1 @ A @ C ) ) =>
% 0.21/0.53             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.53    (~( ![A:$i,B:$i]:
% 0.21/0.53        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53          ( ![C:$i]:
% 0.21/0.53            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53              ( ( ( k3_subset_1 @ A @ B ) = ( k3_subset_1 @ A @ C ) ) =>
% 0.21/0.53                ( ( B ) = ( C ) ) ) ) ) ) )),
% 0.21/0.53    inference('cnf.neg', [status(esa)], [t64_subset_1])).
% 0.21/0.53  thf('8', plain,
% 0.21/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k3_subset_1 @ sk_A @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf(t31_subset_1, axiom,
% 0.21/0.53    (![A:$i,B:$i]:
% 0.21/0.53     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53       ( ![C:$i]:
% 0.21/0.53         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.53           ( ( r1_tarski @ B @ C ) <=>
% 0.21/0.53             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.21/0.53  thf('9', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.21/0.53          | ~ (r1_tarski @ (k3_subset_1 @ X13 @ X12) @ 
% 0.21/0.53               (k3_subset_1 @ X13 @ X14))
% 0.21/0.53          | (r1_tarski @ X14 @ X12)
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.21/0.53  thf('10', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.21/0.53             (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.53          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.53          | (r1_tarski @ sk_C @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.53  thf('11', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('12', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k3_subset_1 @ sk_A @ X0) @ 
% 0.21/0.53             (k3_subset_1 @ sk_A @ sk_B))
% 0.21/0.53          | (r1_tarski @ sk_C @ X0)
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.53  thf('13', plain,
% 0.21/0.53      ((~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.53        | (r1_tarski @ sk_C @ sk_B))),
% 0.21/0.53      inference('sup-', [status(thm)], ['7', '12'])).
% 0.21/0.53  thf('14', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('15', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('16', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.53  thf(t20_xboole_1, axiom,
% 0.21/0.53    (![A:$i,B:$i,C:$i]:
% 0.21/0.53     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.53         ( ![D:$i]:
% 0.21/0.53           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.21/0.53             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.21/0.53       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.53  thf('17', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ X2)
% 0.21/0.53          | (r1_tarski @ (sk_D @ X2 @ X1 @ X0) @ X1)
% 0.21/0.53          | ((X0) = (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.21/0.53  thf('18', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i]:
% 0.21/0.53         (((X0) = (k3_xboole_0 @ X0 @ X1))
% 0.21/0.53          | (r1_tarski @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.53  thf('19', plain,
% 0.21/0.53      (((r1_tarski @ (sk_D @ sk_B @ sk_C @ sk_C) @ sk_C)
% 0.21/0.53        | ((sk_C) = (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['15', '18'])).
% 0.21/0.53  thf('20', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.53  thf('21', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.53  thf('22', plain,
% 0.21/0.53      (((k3_subset_1 @ sk_A @ sk_B) = (k3_subset_1 @ sk_A @ sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('23', plain,
% 0.21/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.53         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.21/0.53          | ~ (r1_tarski @ (k3_subset_1 @ X13 @ X12) @ 
% 0.21/0.53               (k3_subset_1 @ X13 @ X14))
% 0.21/0.53          | (r1_tarski @ X14 @ X12)
% 0.21/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.21/0.53  thf('24', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.21/0.53             (k3_subset_1 @ sk_A @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.53          | (r1_tarski @ X0 @ sk_C)
% 0.21/0.53          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.53  thf('25', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('26', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (~ (r1_tarski @ (k3_subset_1 @ sk_A @ sk_B) @ 
% 0.21/0.53             (k3_subset_1 @ sk_A @ X0))
% 0.21/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.21/0.53          | (r1_tarski @ X0 @ sk_C))),
% 0.21/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.21/0.53  thf('27', plain,
% 0.21/0.53      (((r1_tarski @ sk_B @ sk_C)
% 0.21/0.53        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['21', '26'])).
% 0.21/0.53  thf('28', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('29', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('30', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ X2)
% 0.21/0.53          | (r1_tarski @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.21/0.53          | ((X0) = (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.21/0.53  thf('31', plain,
% 0.21/0.53      (![X0 : $i]:
% 0.21/0.53         (((sk_B) = (k3_xboole_0 @ sk_C @ X0))
% 0.21/0.53          | (r1_tarski @ (sk_D @ X0 @ sk_C @ sk_B) @ X0)
% 0.21/0.53          | ~ (r1_tarski @ sk_B @ X0))),
% 0.21/0.53      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.53  thf('32', plain,
% 0.21/0.53      (((r1_tarski @ (sk_D @ sk_B @ sk_C @ sk_B) @ sk_B)
% 0.21/0.53        | ((sk_B) = (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.21/0.53      inference('sup-', [status(thm)], ['20', '31'])).
% 0.21/0.53  thf('33', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ X2)
% 0.21/0.53          | ~ (r1_tarski @ (sk_D @ X2 @ X1 @ X0) @ X0)
% 0.21/0.53          | ((X0) = (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.21/0.53  thf('34', plain,
% 0.21/0.53      ((((sk_B) = (k3_xboole_0 @ sk_C @ sk_B))
% 0.21/0.53        | ((sk_B) = (k3_xboole_0 @ sk_C @ sk_B))
% 0.21/0.53        | ~ (r1_tarski @ sk_B @ sk_B)
% 0.21/0.53        | ~ (r1_tarski @ sk_B @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.53  thf('35', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.53  thf('36', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.21/0.53      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.53  thf('37', plain,
% 0.21/0.53      ((((sk_B) = (k3_xboole_0 @ sk_C @ sk_B))
% 0.21/0.53        | ((sk_B) = (k3_xboole_0 @ sk_C @ sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.21/0.53  thf('38', plain, (((sk_B) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.53  thf('39', plain,
% 0.21/0.53      (((r1_tarski @ (sk_D @ sk_B @ sk_C @ sk_C) @ sk_C) | ((sk_C) = (sk_B)))),
% 0.21/0.53      inference('demod', [status(thm)], ['19', '38'])).
% 0.21/0.53  thf('40', plain, (((sk_B) != (sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('41', plain, ((r1_tarski @ (sk_D @ sk_B @ sk_C @ sk_C) @ sk_C)),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.21/0.53  thf('42', plain,
% 0.21/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.53         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.53          | ~ (r1_tarski @ X0 @ X2)
% 0.21/0.53          | ~ (r1_tarski @ (sk_D @ X2 @ X1 @ X0) @ X0)
% 0.21/0.53          | ((X0) = (k3_xboole_0 @ X1 @ X2)))),
% 0.21/0.53      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.21/0.53  thf('43', plain,
% 0.21/0.53      ((((sk_C) = (k3_xboole_0 @ sk_C @ sk_B))
% 0.21/0.53        | ~ (r1_tarski @ sk_C @ sk_B)
% 0.21/0.53        | ~ (r1_tarski @ sk_C @ sk_C))),
% 0.21/0.53      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.53  thf('44', plain, (((sk_B) = (k3_xboole_0 @ sk_C @ sk_B))),
% 0.21/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.53  thf('45', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.21/0.53      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.53  thf('46', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.53      inference('sup-', [status(thm)], ['0', '6'])).
% 0.21/0.53  thf('47', plain, (((sk_C) = (sk_B))),
% 0.21/0.53      inference('demod', [status(thm)], ['43', '44', '45', '46'])).
% 0.21/0.53  thf('48', plain, (((sk_B) != (sk_C))),
% 0.21/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.53  thf('49', plain, ($false),
% 0.21/0.53      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.21/0.53  
% 0.21/0.53  % SZS output end Refutation
% 0.21/0.53  
% 0.21/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
