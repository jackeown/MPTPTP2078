%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hkpq7RfInL

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:48 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 184 expanded)
%              Number of leaves         :   21 (  65 expanded)
%              Depth                    :   15
%              Number of atoms          :  484 (1424 expanded)
%              Number of equality atoms :   37 (  98 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('0',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t106_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) )
     => ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t40_subset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( ( r1_tarski @ B @ C )
          & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
       => ( B = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
       => ( ( ( r1_tarski @ B @ C )
            & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) )
         => ( B = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t40_subset_1])).

thf('5',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k3_subset_1 @ X20 @ X21 )
        = ( k4_xboole_0 @ X20 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('8',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_tarski @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['5','10'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_xboole_0 @ X17 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_xboole_0 @ sk_B @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('16',plain,
    ( ( k4_xboole_0 @ sk_B @ k1_xboole_0 )
    = sk_B ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('18',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('19',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('22',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ sk_B @ ( k3_subset_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k3_subset_1 @ sk_A @ sk_C )
    = ( k4_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X8 @ X10 )
      | ~ ( r1_tarski @ X8 @ ( k4_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t106_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k3_subset_1 @ sk_A @ sk_C ) )
      | ( r1_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    r1_xboole_0 @ sk_B @ sk_C ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('34',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k4_xboole_0 @ X12 @ ( k4_xboole_0 @ X12 @ X13 ) )
      = ( k3_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('40',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('41',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['38','42'])).

thf('44',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('45',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('46',plain,
    ( ( k3_xboole_0 @ sk_B @ k1_xboole_0 )
    = ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,
    ( ( k3_xboole_0 @ sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['27','47'])).

thf('49',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['18','48'])).

thf('50',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['32','33'])).

thf('51',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ( r1_xboole_0 @ X17 @ ( k4_xboole_0 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    r1_xboole_0 @ sk_B @ sk_B ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('56',plain,
    ( ( k4_xboole_0 @ sk_B @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    k1_xboole_0 = sk_B ),
    inference('sup+',[status(thm)],['49','56'])).

thf('58',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Hkpq7RfInL
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.37/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.60  % Solved by: fo/fo7.sh
% 0.37/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.60  % done 240 iterations in 0.138s
% 0.37/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.60  % SZS output start Refutation
% 0.37/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.60  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.37/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.37/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.60  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.60  thf('0', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.37/0.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.60  thf(t106_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) =>
% 0.37/0.60       ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ))).
% 0.37/0.60  thf('1', plain,
% 0.37/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X8 @ X10)
% 0.37/0.60          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.37/0.60  thf('2', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.37/0.60      inference('sup-', [status(thm)], ['0', '1'])).
% 0.37/0.60  thf(t83_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.60  thf('3', plain,
% 0.37/0.60      (![X14 : $i, X15 : $i]:
% 0.37/0.60         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.37/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.60  thf('4', plain,
% 0.37/0.60      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.60  thf(t40_subset_1, conjecture,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.60       ( ( ( r1_tarski @ B @ C ) & ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.37/0.60         ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.37/0.60        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.60          ( ( ( r1_tarski @ B @ C ) & 
% 0.37/0.60              ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) =>
% 0.37/0.60            ( ( B ) = ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.60    inference('cnf.neg', [status(esa)], [t40_subset_1])).
% 0.37/0.60  thf('5', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('6', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf(d5_subset_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.60       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.37/0.60  thf('7', plain,
% 0.37/0.60      (![X20 : $i, X21 : $i]:
% 0.37/0.60         (((k3_subset_1 @ X20 @ X21) = (k4_xboole_0 @ X20 @ X21))
% 0.37/0.60          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X20)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.37/0.60  thf('8', plain,
% 0.37/0.60      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.37/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.60  thf('9', plain,
% 0.37/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.60         ((r1_tarski @ X8 @ X9) | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.37/0.60  thf('10', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.37/0.60          | (r1_tarski @ X0 @ sk_A))),
% 0.37/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.60  thf('11', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.37/0.60      inference('sup-', [status(thm)], ['5', '10'])).
% 0.37/0.60  thf(t85_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 0.37/0.60  thf('12', plain,
% 0.37/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.60         (~ (r1_tarski @ X17 @ X18)
% 0.37/0.60          | (r1_xboole_0 @ X17 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.37/0.60  thf('13', plain,
% 0.37/0.60      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_A))),
% 0.37/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.60  thf('14', plain, ((r1_xboole_0 @ sk_B @ k1_xboole_0)),
% 0.37/0.60      inference('sup+', [status(thm)], ['4', '13'])).
% 0.37/0.60  thf('15', plain,
% 0.37/0.60      (![X14 : $i, X15 : $i]:
% 0.37/0.60         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.37/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.60  thf('16', plain, (((k4_xboole_0 @ sk_B @ k1_xboole_0) = (sk_B))),
% 0.37/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.37/0.60  thf(t48_xboole_1, axiom,
% 0.37/0.60    (![A:$i,B:$i]:
% 0.37/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.37/0.60  thf('17', plain,
% 0.37/0.60      (![X12 : $i, X13 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.60           = (k3_xboole_0 @ X12 @ X13))),
% 0.37/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.60  thf('18', plain,
% 0.37/0.60      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.37/0.60      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.60  thf(d5_xboole_0, axiom,
% 0.37/0.60    (![A:$i,B:$i,C:$i]:
% 0.37/0.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.37/0.60       ( ![D:$i]:
% 0.37/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.37/0.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.37/0.60  thf('19', plain,
% 0.37/0.60      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.37/0.60         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.37/0.60          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.37/0.60          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.37/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.60  thf('20', plain,
% 0.37/0.60      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.60  thf('21', plain,
% 0.37/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.60          | ~ (r2_hidden @ X4 @ X2)
% 0.37/0.60          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.60  thf('22', plain,
% 0.37/0.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X4 @ X2)
% 0.37/0.60          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.60  thf('23', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['20', '22'])).
% 0.37/0.60  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.37/0.60      inference('condensation', [status(thm)], ['23'])).
% 0.37/0.60  thf('25', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.37/0.60          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.37/0.60      inference('sup-', [status(thm)], ['19', '24'])).
% 0.37/0.60  thf('26', plain,
% 0.37/0.60      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.37/0.60      inference('sup-', [status(thm)], ['2', '3'])).
% 0.37/0.60  thf('27', plain,
% 0.37/0.60      (![X0 : $i, X1 : $i]:
% 0.37/0.60         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.37/0.60          | ((X1) = (k1_xboole_0)))),
% 0.37/0.60      inference('demod', [status(thm)], ['25', '26'])).
% 0.37/0.60  thf('28', plain, ((r1_tarski @ sk_B @ (k3_subset_1 @ sk_A @ sk_C))),
% 0.37/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.60  thf('29', plain,
% 0.37/0.60      (((k3_subset_1 @ sk_A @ sk_C) = (k4_xboole_0 @ sk_A @ sk_C))),
% 0.37/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.37/0.60  thf('30', plain,
% 0.37/0.60      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.37/0.60         ((r1_xboole_0 @ X8 @ X10)
% 0.37/0.60          | ~ (r1_tarski @ X8 @ (k4_xboole_0 @ X9 @ X10)))),
% 0.37/0.60      inference('cnf', [status(esa)], [t106_xboole_1])).
% 0.37/0.60  thf('31', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (~ (r1_tarski @ X0 @ (k3_subset_1 @ sk_A @ sk_C))
% 0.37/0.60          | (r1_xboole_0 @ X0 @ sk_C))),
% 0.37/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.37/0.60  thf('32', plain, ((r1_xboole_0 @ sk_B @ sk_C)),
% 0.37/0.60      inference('sup-', [status(thm)], ['28', '31'])).
% 0.37/0.60  thf('33', plain,
% 0.37/0.60      (![X14 : $i, X15 : $i]:
% 0.37/0.60         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.37/0.60      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.60  thf('34', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.37/0.60      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.60  thf('35', plain,
% 0.37/0.60      (![X12 : $i, X13 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.60           = (k3_xboole_0 @ X12 @ X13))),
% 0.37/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.60  thf('36', plain,
% 0.37/0.60      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.60      inference('sup+', [status(thm)], ['34', '35'])).
% 0.37/0.60  thf('37', plain,
% 0.37/0.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X4 @ X2)
% 0.37/0.60          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.37/0.60  thf('38', plain,
% 0.37/0.60      (![X0 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_C))
% 0.37/0.60          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.37/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.60  thf('39', plain,
% 0.37/0.60      (![X12 : $i, X13 : $i]:
% 0.37/0.60         ((k4_xboole_0 @ X12 @ (k4_xboole_0 @ X12 @ X13))
% 0.37/0.60           = (k3_xboole_0 @ X12 @ X13))),
% 0.37/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.37/0.60  thf('40', plain,
% 0.37/0.60      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.37/0.60         (~ (r2_hidden @ X4 @ X3)
% 0.37/0.60          | (r2_hidden @ X4 @ X1)
% 0.37/0.60          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.37/0.60  thf('41', plain,
% 0.37/0.60      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.37/0.60         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.37/0.61      inference('simplify', [status(thm)], ['40'])).
% 0.37/0.61  thf('42', plain,
% 0.37/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.61         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.37/0.61      inference('sup-', [status(thm)], ['39', '41'])).
% 0.37/0.61  thf('43', plain,
% 0.37/0.61      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.61      inference('clc', [status(thm)], ['38', '42'])).
% 0.37/0.61  thf('44', plain,
% 0.37/0.61      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.37/0.61      inference('sup+', [status(thm)], ['16', '17'])).
% 0.37/0.61  thf('45', plain,
% 0.37/0.61      (((k4_xboole_0 @ sk_B @ sk_B) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.61      inference('sup+', [status(thm)], ['34', '35'])).
% 0.37/0.61  thf('46', plain,
% 0.37/0.61      (((k3_xboole_0 @ sk_B @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_C))),
% 0.37/0.61      inference('sup+', [status(thm)], ['44', '45'])).
% 0.37/0.61  thf('47', plain,
% 0.37/0.61      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['43', '46'])).
% 0.37/0.61  thf('48', plain, (((k3_xboole_0 @ sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.61      inference('sup-', [status(thm)], ['27', '47'])).
% 0.37/0.61  thf('49', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (k1_xboole_0))),
% 0.37/0.61      inference('demod', [status(thm)], ['18', '48'])).
% 0.37/0.61  thf('50', plain, (((k4_xboole_0 @ sk_B @ sk_C) = (sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.61  thf('51', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('52', plain,
% 0.37/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.37/0.61         (~ (r1_tarski @ X17 @ X18)
% 0.37/0.61          | (r1_xboole_0 @ X17 @ (k4_xboole_0 @ X19 @ X18)))),
% 0.37/0.61      inference('cnf', [status(esa)], [t85_xboole_1])).
% 0.37/0.61  thf('53', plain,
% 0.37/0.61      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_C))),
% 0.37/0.61      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.61  thf('54', plain, ((r1_xboole_0 @ sk_B @ sk_B)),
% 0.37/0.61      inference('sup+', [status(thm)], ['50', '53'])).
% 0.37/0.61  thf('55', plain,
% 0.37/0.61      (![X14 : $i, X15 : $i]:
% 0.37/0.61         (((k4_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_xboole_0 @ X14 @ X15))),
% 0.37/0.61      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.61  thf('56', plain, (((k4_xboole_0 @ sk_B @ sk_B) = (sk_B))),
% 0.37/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.37/0.61  thf('57', plain, (((k1_xboole_0) = (sk_B))),
% 0.37/0.61      inference('sup+', [status(thm)], ['49', '56'])).
% 0.37/0.61  thf('58', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.61  thf('59', plain, ($false),
% 0.37/0.61      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.37/0.61  
% 0.37/0.61  % SZS output end Refutation
% 0.37/0.61  
% 0.37/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
