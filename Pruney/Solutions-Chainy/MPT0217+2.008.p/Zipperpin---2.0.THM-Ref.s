%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.76N1RJ4U4H

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:00 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 138 expanded)
%              Number of leaves         :   21 (  52 expanded)
%              Depth                    :   14
%              Number of atoms          :  626 (1185 expanded)
%              Number of equality atoms :   63 ( 128 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t42_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t136_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != B )
        & ( A != C )
        & ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) )
         != ( k2_tarski @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( X18 = X17 )
      | ( ( k4_xboole_0 @ ( k1_enumset1 @ X18 @ X17 @ X19 ) @ ( k1_tarski @ X18 ) )
        = ( k2_tarski @ X17 @ X19 ) )
      | ( X18 = X19 ) ) ),
    inference(cnf,[status(esa)],[t136_enumset1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t137_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X21 @ X20 ) @ ( k2_tarski @ X22 @ X20 ) )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t137_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k1_enumset1 @ X0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t6_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k2_xboole_0 @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) )
      = ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf(t10_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( ( k2_tarski @ A @ B )
          = ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( ( k2_tarski @ A @ B )
            = ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t10_zfmisc_1])).

thf('23',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k2_tarski @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_A @ sk_B )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ sk_A @ sk_B )
      = ( k1_enumset1 @ X0 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X21 @ X20 ) @ ( k2_tarski @ X22 @ X20 ) )
      = ( k1_enumset1 @ X20 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t137_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_tarski @ sk_A @ X0 ) @ ( k1_enumset1 @ X0 @ sk_C @ sk_D ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_D ) @ ( k2_tarski @ sk_D @ sk_C ) ),
    inference('sup+',[status(thm)],['22','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('34',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_D ) @ ( k1_enumset1 @ sk_D @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X2 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

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
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k2_tarski @ sk_D @ sk_A ) @ ( k1_enumset1 @ sk_D @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X25 @ X26 @ X27 )
      = ( k2_xboole_0 @ ( k1_tarski @ X25 ) @ ( k2_tarski @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t42_enumset1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      | ~ ( r1_tarski @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X3 @ ( k1_tarski @ X2 ) ) @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_tarski @ sk_D @ sk_A ) @ ( k1_tarski @ sk_D ) ) @ ( k2_tarski @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X0 @ X1 @ X0 )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_enumset1 @ X1 @ X0 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('47',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_enumset1 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( k2_tarski @ sk_D @ sk_A ) @ ( k1_tarski @ sk_D ) ) @ ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','48'])).

thf('50',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( sk_D = sk_A ) ),
    inference('sup+',[status(thm)],['9','49'])).

thf('51',plain,(
    sk_A != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('53',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X33 = X32 )
      | ~ ( r1_tarski @ ( k1_tarski @ X33 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('54',plain,(
    sk_A = sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.76N1RJ4U4H
% 0.11/0.33  % Computer   : n003.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 16:08:42 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.34  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 630 iterations in 0.283s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.49/0.72  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.49/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(sk_D_type, type, sk_D: $i).
% 0.49/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.72  thf(t69_enumset1, axiom,
% 0.49/0.72    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.49/0.72  thf('0', plain, (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.49/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.72  thf(t42_enumset1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( k1_enumset1 @ A @ B @ C ) =
% 0.49/0.72       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) ))).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X25 @ X26 @ X27)
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X25) @ (k2_tarski @ X26 @ X27)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.49/0.72  thf('2', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X1 @ X0 @ X0)
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['0', '1'])).
% 0.49/0.72  thf(t41_enumset1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( k2_tarski @ A @ B ) =
% 0.49/0.72       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.49/0.72  thf('3', plain,
% 0.49/0.72      (![X23 : $i, X24 : $i]:
% 0.49/0.72         ((k2_tarski @ X23 @ X24)
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X24)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.49/0.72  thf('4', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.72  thf(t136_enumset1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ~( ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) & 
% 0.49/0.72          ( ( k4_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ A ) ) !=
% 0.49/0.72            ( k2_tarski @ B @ C ) ) ) ))).
% 0.49/0.72  thf('5', plain,
% 0.49/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.72         (((X18) = (X17))
% 0.49/0.72          | ((k4_xboole_0 @ (k1_enumset1 @ X18 @ X17 @ X19) @ (k1_tarski @ X18))
% 0.49/0.72              = (k2_tarski @ X17 @ X19))
% 0.49/0.72          | ((X18) = (X19)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t136_enumset1])).
% 0.49/0.72  thf('6', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.49/0.72            = (k2_tarski @ X0 @ X0))
% 0.49/0.72          | ((X1) = (X0))
% 0.49/0.72          | ((X1) = (X0)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['4', '5'])).
% 0.49/0.72  thf('7', plain, (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.49/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.72  thf('8', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.49/0.72            = (k1_tarski @ X0))
% 0.49/0.72          | ((X1) = (X0))
% 0.49/0.72          | ((X1) = (X0)))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.49/0.72  thf('9', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (((X1) = (X0))
% 0.49/0.72          | ((k4_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X1))
% 0.49/0.72              = (k1_tarski @ X0)))),
% 0.49/0.72      inference('simplify', [status(thm)], ['8'])).
% 0.49/0.72  thf('10', plain,
% 0.49/0.72      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.49/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.72  thf(t137_enumset1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( k2_xboole_0 @ ( k2_tarski @ B @ A ) @ ( k2_tarski @ C @ A ) ) =
% 0.49/0.72       ( k1_enumset1 @ A @ B @ C ) ))).
% 0.49/0.72  thf('11', plain,
% 0.49/0.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.72         ((k2_xboole_0 @ (k2_tarski @ X21 @ X20) @ (k2_tarski @ X22 @ X20))
% 0.49/0.72           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.49/0.72      inference('cnf', [status(esa)], [t137_enumset1])).
% 0.49/0.72  thf('12', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.49/0.72           = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.49/0.72      inference('sup+', [status(thm)], ['10', '11'])).
% 0.49/0.72  thf('13', plain,
% 0.49/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X25 @ X26 @ X27)
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X25) @ (k2_tarski @ X26 @ X27)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.49/0.72  thf('14', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X0 @ X1 @ X0) = (k1_enumset1 @ X0 @ X0 @ X1))),
% 0.49/0.72      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.72  thf('15', plain,
% 0.49/0.72      (![X23 : $i, X24 : $i]:
% 0.49/0.72         ((k2_tarski @ X23 @ X24)
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X24)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.49/0.72  thf(t6_xboole_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( k2_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.49/0.72  thf('16', plain,
% 0.49/0.72      (![X13 : $i, X14 : $i]:
% 0.49/0.72         ((k2_xboole_0 @ X13 @ (k2_xboole_0 @ X13 @ X14))
% 0.49/0.72           = (k2_xboole_0 @ X13 @ X14))),
% 0.49/0.72      inference('cnf', [status(esa)], [t6_xboole_1])).
% 0.49/0.72  thf('17', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['15', '16'])).
% 0.49/0.72  thf('18', plain,
% 0.49/0.72      (![X23 : $i, X24 : $i]:
% 0.49/0.72         ((k2_tarski @ X23 @ X24)
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X24)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.49/0.72  thf('19', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))
% 0.49/0.72           = (k2_tarski @ X1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['17', '18'])).
% 0.49/0.72  thf('20', plain,
% 0.49/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X25 @ X26 @ X27)
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X25) @ (k2_tarski @ X26 @ X27)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.49/0.72  thf('21', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['19', '20'])).
% 0.49/0.72  thf('22', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.49/0.72      inference('sup+', [status(thm)], ['14', '21'])).
% 0.49/0.72  thf(t10_zfmisc_1, conjecture,
% 0.49/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.72     ( ~( ( ( k2_tarski @ A @ B ) = ( k2_tarski @ C @ D ) ) & 
% 0.49/0.72          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.72        ( ~( ( ( k2_tarski @ A @ B ) = ( k2_tarski @ C @ D ) ) & 
% 0.49/0.72             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t10_zfmisc_1])).
% 0.49/0.72  thf('23', plain, (((k2_tarski @ sk_A @ sk_B) = (k2_tarski @ sk_C @ sk_D))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('24', plain,
% 0.49/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X25 @ X26 @ X27)
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X25) @ (k2_tarski @ X26 @ X27)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.49/0.72  thf('25', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X0 @ sk_A @ sk_B)
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ sk_C @ sk_D)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['23', '24'])).
% 0.49/0.72  thf('26', plain,
% 0.49/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X25 @ X26 @ X27)
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X25) @ (k2_tarski @ X26 @ X27)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.49/0.72  thf('27', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X0 @ sk_A @ sk_B) = (k1_enumset1 @ X0 @ sk_C @ sk_D))),
% 0.49/0.72      inference('demod', [status(thm)], ['25', '26'])).
% 0.49/0.72  thf('28', plain,
% 0.49/0.72      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.72         ((k2_xboole_0 @ (k2_tarski @ X21 @ X20) @ (k2_tarski @ X22 @ X20))
% 0.49/0.72           = (k1_enumset1 @ X20 @ X21 @ X22))),
% 0.49/0.72      inference('cnf', [status(esa)], [t137_enumset1])).
% 0.49/0.72  thf(t7_xboole_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.49/0.72  thf('29', plain,
% 0.49/0.72      (![X15 : $i, X16 : $i]: (r1_tarski @ X15 @ (k2_xboole_0 @ X15 @ X16))),
% 0.49/0.72      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.49/0.72  thf('30', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (r1_tarski @ (k2_tarski @ X1 @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['28', '29'])).
% 0.49/0.72  thf('31', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (r1_tarski @ (k2_tarski @ sk_A @ X0) @ 
% 0.49/0.72          (k1_enumset1 @ X0 @ sk_C @ sk_D))),
% 0.49/0.72      inference('sup+', [status(thm)], ['27', '30'])).
% 0.49/0.72  thf('32', plain,
% 0.49/0.72      ((r1_tarski @ (k2_tarski @ sk_A @ sk_D) @ (k2_tarski @ sk_D @ sk_C))),
% 0.49/0.72      inference('sup+', [status(thm)], ['22', '31'])).
% 0.49/0.72  thf('33', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.72  thf('34', plain,
% 0.49/0.72      ((r1_tarski @ (k2_tarski @ sk_A @ sk_D) @ 
% 0.49/0.72        (k1_enumset1 @ sk_D @ sk_C @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['32', '33'])).
% 0.49/0.72  thf('35', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.72  thf('36', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (r1_tarski @ (k2_tarski @ X1 @ X2) @ (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['28', '29'])).
% 0.49/0.72  thf('37', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         (r1_tarski @ (k2_tarski @ X0 @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['35', '36'])).
% 0.49/0.72  thf(t1_xboole_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.49/0.72       ( r1_tarski @ A @ C ) ))).
% 0.49/0.72  thf('38', plain,
% 0.49/0.72      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.49/0.72         (~ (r1_tarski @ X3 @ X4)
% 0.49/0.72          | ~ (r1_tarski @ X4 @ X5)
% 0.49/0.72          | (r1_tarski @ X3 @ X5))),
% 0.49/0.72      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.49/0.72  thf('39', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         ((r1_tarski @ (k2_tarski @ X0 @ X1) @ X2)
% 0.49/0.72          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.49/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.72  thf('40', plain,
% 0.49/0.72      ((r1_tarski @ (k2_tarski @ sk_D @ sk_A) @ 
% 0.49/0.72        (k1_enumset1 @ sk_D @ sk_C @ sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['34', '39'])).
% 0.49/0.72  thf('41', plain,
% 0.49/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X25 @ X26 @ X27)
% 0.49/0.72           = (k2_xboole_0 @ (k1_tarski @ X25) @ (k2_tarski @ X26 @ X27)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t42_enumset1])).
% 0.49/0.72  thf(t43_xboole_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.49/0.72       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.49/0.72  thf('42', plain,
% 0.49/0.72      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.49/0.72         ((r1_tarski @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 0.49/0.72          | ~ (r1_tarski @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.49/0.72  thf('43', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.72         (~ (r1_tarski @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 0.49/0.72          | (r1_tarski @ (k4_xboole_0 @ X3 @ (k1_tarski @ X2)) @ 
% 0.49/0.72             (k2_tarski @ X1 @ X0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['41', '42'])).
% 0.49/0.72  thf('44', plain,
% 0.49/0.72      ((r1_tarski @ 
% 0.49/0.72        (k4_xboole_0 @ (k2_tarski @ sk_D @ sk_A) @ (k1_tarski @ sk_D)) @ 
% 0.49/0.72        (k2_tarski @ sk_C @ sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['40', '43'])).
% 0.49/0.72  thf('45', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X0 @ X1 @ X0) = (k2_tarski @ X0 @ X1))),
% 0.49/0.72      inference('sup+', [status(thm)], ['14', '21'])).
% 0.49/0.72  thf('46', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((k1_enumset1 @ X1 @ X0 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.49/0.72      inference('demod', [status(thm)], ['2', '3'])).
% 0.49/0.72  thf('47', plain,
% 0.49/0.72      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.49/0.72      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.72  thf('48', plain,
% 0.49/0.72      (![X0 : $i]: ((k1_enumset1 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.49/0.72      inference('sup+', [status(thm)], ['46', '47'])).
% 0.49/0.72  thf('49', plain,
% 0.49/0.72      ((r1_tarski @ 
% 0.49/0.72        (k4_xboole_0 @ (k2_tarski @ sk_D @ sk_A) @ (k1_tarski @ sk_D)) @ 
% 0.49/0.72        (k1_tarski @ sk_C))),
% 0.49/0.72      inference('demod', [status(thm)], ['44', '45', '48'])).
% 0.49/0.72  thf('50', plain,
% 0.49/0.72      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))
% 0.49/0.72        | ((sk_D) = (sk_A)))),
% 0.49/0.72      inference('sup+', [status(thm)], ['9', '49'])).
% 0.49/0.72  thf('51', plain, (((sk_A) != (sk_D))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('52', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C))),
% 0.49/0.72      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.49/0.72  thf(t6_zfmisc_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.49/0.72       ( ( A ) = ( B ) ) ))).
% 0.49/0.72  thf('53', plain,
% 0.49/0.72      (![X32 : $i, X33 : $i]:
% 0.49/0.72         (((X33) = (X32))
% 0.49/0.72          | ~ (r1_tarski @ (k1_tarski @ X33) @ (k1_tarski @ X32)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.49/0.72  thf('54', plain, (((sk_A) = (sk_C))),
% 0.49/0.72      inference('sup-', [status(thm)], ['52', '53'])).
% 0.49/0.72  thf('55', plain, (((sk_A) != (sk_C))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf('56', plain, ($false),
% 0.49/0.72      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.49/0.72  
% 0.49/0.72  % SZS output end Refutation
% 0.49/0.72  
% 0.49/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
