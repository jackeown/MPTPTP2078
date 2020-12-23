%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XJ24I7gAgz

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:44 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 156 expanded)
%              Number of leaves         :   27 (  57 expanded)
%              Depth                    :   15
%              Number of atoms          :  507 (1243 expanded)
%              Number of equality atoms :   71 ( 218 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t44_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k1_tarski @ A )
          = ( k2_xboole_0 @ B @ C ) )
        & ( B != C )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k1_tarski @ A )
            = ( k2_xboole_0 @ B @ C ) )
          & ( B != C )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_zfmisc_1])).

thf('0',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('2',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k2_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('5',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ X9 @ ( k3_tarski @ ( k2_tarski @ X9 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_B_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('8',plain,(
    ! [X54: $i,X55: $i] :
      ( ( X55
        = ( k1_tarski @ X54 ) )
      | ( X55 = k1_xboole_0 )
      | ~ ( r1_tarski @ X55 @ ( k1_tarski @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('9',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_B_1
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_B_1
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,
    ( sk_B_1
    = ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['2','11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k3_tarski @ ( k2_tarski @ X3 @ X1 ) ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C ) @ sk_B_1 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','19'])).

thf('21',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    r2_hidden @ ( sk_B @ sk_C ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['20','21'])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( X12 = X13 )
      | ( X12 = X14 )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('24',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
    ! [X23: $i] :
      ( ( k2_tarski @ X23 @ X23 )
      = ( k1_tarski @ X23 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('28',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_A )
      | ( X0 = sk_A )
      | ( X0 = sk_A )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0 = sk_A ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( sk_B @ sk_C )
    = sk_A ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('36',plain,(
    ! [X51: $i,X53: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X51 ) @ X53 )
      | ~ ( r2_hidden @ X51 @ X53 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_xboole_0 @ X8 @ X7 )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,(
    ! [X57: $i,X58: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X57 @ X58 ) )
      = ( k2_xboole_0 @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k3_tarski @ ( k2_tarski @ X8 @ X7 ) )
        = X7 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ ( k1_tarski @ sk_A ) @ sk_C ) )
      = sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,
    ( sk_B_1
    = ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('44',plain,
    ( ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) )
      = sk_C )
    | ( sk_C = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k3_tarski @ ( k2_tarski @ sk_B_1 @ sk_C ) )
    = sk_C ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

thf('47',plain,(
    sk_B_1 = sk_C ),
    inference('sup+',[status(thm)],['12','46'])).

thf('48',plain,(
    sk_B_1 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XJ24I7gAgz
% 0.14/0.36  % Computer   : n013.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 09:32:10 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.23/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.55  % Solved by: fo/fo7.sh
% 0.23/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.55  % done 368 iterations in 0.098s
% 0.23/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.55  % SZS output start Refutation
% 0.23/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.23/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.23/0.55  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.23/0.55  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.23/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.23/0.55  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.23/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.23/0.55  thf(t44_zfmisc_1, conjecture,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.23/0.55          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.23/0.55          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.23/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.23/0.55        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.23/0.55             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.23/0.55             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.23/0.55    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.23/0.55  thf('0', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf(l51_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.55  thf('1', plain,
% 0.23/0.55      (![X57 : $i, X58 : $i]:
% 0.23/0.55         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 0.23/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.23/0.55  thf('2', plain,
% 0.23/0.55      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C)))),
% 0.23/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.55  thf('3', plain,
% 0.23/0.55      (((k1_tarski @ sk_A) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C)))),
% 0.23/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.23/0.55  thf(t7_xboole_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.23/0.55  thf('4', plain,
% 0.23/0.55      (![X9 : $i, X10 : $i]: (r1_tarski @ X9 @ (k2_xboole_0 @ X9 @ X10))),
% 0.23/0.55      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.23/0.55  thf('5', plain,
% 0.23/0.55      (![X57 : $i, X58 : $i]:
% 0.23/0.55         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 0.23/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.23/0.55  thf('6', plain,
% 0.23/0.55      (![X9 : $i, X10 : $i]:
% 0.23/0.55         (r1_tarski @ X9 @ (k3_tarski @ (k2_tarski @ X9 @ X10)))),
% 0.23/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.23/0.55  thf('7', plain, ((r1_tarski @ sk_B_1 @ (k1_tarski @ sk_A))),
% 0.23/0.55      inference('sup+', [status(thm)], ['3', '6'])).
% 0.23/0.55  thf(l3_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.23/0.55       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.23/0.55  thf('8', plain,
% 0.23/0.55      (![X54 : $i, X55 : $i]:
% 0.23/0.55         (((X55) = (k1_tarski @ X54))
% 0.23/0.55          | ((X55) = (k1_xboole_0))
% 0.23/0.55          | ~ (r1_tarski @ X55 @ (k1_tarski @ X54)))),
% 0.23/0.55      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.23/0.55  thf('9', plain,
% 0.23/0.55      ((((sk_B_1) = (k1_xboole_0)) | ((sk_B_1) = (k1_tarski @ sk_A)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.55  thf('10', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('11', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.23/0.55  thf('12', plain, (((sk_B_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C)))),
% 0.23/0.55      inference('demod', [status(thm)], ['2', '11'])).
% 0.23/0.55  thf('13', plain, (((sk_B_1) = (k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C)))),
% 0.23/0.55      inference('demod', [status(thm)], ['2', '11'])).
% 0.23/0.55  thf(t7_xboole_0, axiom,
% 0.23/0.55    (![A:$i]:
% 0.23/0.55     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.23/0.55          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.23/0.55  thf('14', plain,
% 0.23/0.55      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.23/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.23/0.55  thf(d3_xboole_0, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i]:
% 0.23/0.55     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.23/0.55       ( ![D:$i]:
% 0.23/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.23/0.55           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.23/0.55  thf('15', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.23/0.55          | (r2_hidden @ X0 @ X2)
% 0.23/0.55          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.23/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.23/0.55  thf('16', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.23/0.55         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.23/0.55      inference('simplify', [status(thm)], ['15'])).
% 0.23/0.55  thf('17', plain,
% 0.23/0.55      (![X57 : $i, X58 : $i]:
% 0.23/0.55         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 0.23/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.23/0.55  thf('18', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.23/0.55         ((r2_hidden @ X0 @ (k3_tarski @ (k2_tarski @ X3 @ X1)))
% 0.23/0.55          | ~ (r2_hidden @ X0 @ X1))),
% 0.23/0.55      inference('demod', [status(thm)], ['16', '17'])).
% 0.23/0.55  thf('19', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (((X0) = (k1_xboole_0))
% 0.23/0.55          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ (k2_tarski @ X1 @ X0))))),
% 0.23/0.55      inference('sup-', [status(thm)], ['14', '18'])).
% 0.23/0.55  thf('20', plain,
% 0.23/0.55      (((r2_hidden @ (sk_B @ sk_C) @ sk_B_1) | ((sk_C) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup+', [status(thm)], ['13', '19'])).
% 0.23/0.55  thf('21', plain, (((sk_C) != (k1_xboole_0))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('22', plain, ((r2_hidden @ (sk_B @ sk_C) @ sk_B_1)),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['20', '21'])).
% 0.23/0.55  thf(d1_enumset1, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.23/0.55       ( ![E:$i]:
% 0.23/0.55         ( ( r2_hidden @ E @ D ) <=>
% 0.23/0.55           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.23/0.55  thf(zf_stmt_1, axiom,
% 0.23/0.55    (![E:$i,C:$i,B:$i,A:$i]:
% 0.23/0.55     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.23/0.55       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.23/0.55  thf('23', plain,
% 0.23/0.55      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.23/0.55         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.23/0.55          | ((X12) = (X13))
% 0.23/0.55          | ((X12) = (X14))
% 0.23/0.55          | ((X12) = (X15)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.23/0.55  thf('24', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.23/0.55  thf(t69_enumset1, axiom,
% 0.23/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.55  thf('25', plain,
% 0.23/0.55      (![X23 : $i]: ((k2_tarski @ X23 @ X23) = (k1_tarski @ X23))),
% 0.23/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.55  thf(t70_enumset1, axiom,
% 0.23/0.55    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.23/0.55  thf('26', plain,
% 0.23/0.55      (![X24 : $i, X25 : $i]:
% 0.23/0.55         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.23/0.55      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.23/0.55  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.23/0.55  thf(zf_stmt_3, axiom,
% 0.23/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.55     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.23/0.55       ( ![E:$i]:
% 0.23/0.55         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.23/0.55  thf('27', plain,
% 0.23/0.55      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X21 @ X20)
% 0.23/0.55          | ~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.23/0.55          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.23/0.55  thf('28', plain,
% 0.23/0.55      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.23/0.55         (~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.23/0.55          | ~ (r2_hidden @ X21 @ (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.23/0.55      inference('simplify', [status(thm)], ['27'])).
% 0.23/0.55  thf('29', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.23/0.55          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.23/0.55      inference('sup-', [status(thm)], ['26', '28'])).
% 0.23/0.55  thf('30', plain,
% 0.23/0.55      (![X0 : $i, X1 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.23/0.55          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['25', '29'])).
% 0.23/0.55  thf('31', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.23/0.55          | ~ (zip_tseitin_0 @ X0 @ sk_A @ sk_A @ sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['24', '30'])).
% 0.23/0.55  thf('32', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((X0) = (sk_A))
% 0.23/0.55          | ((X0) = (sk_A))
% 0.23/0.55          | ((X0) = (sk_A))
% 0.23/0.55          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.23/0.55      inference('sup-', [status(thm)], ['23', '31'])).
% 0.23/0.55  thf('33', plain,
% 0.23/0.55      (![X0 : $i]: (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (sk_A)))),
% 0.23/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.23/0.55  thf('34', plain, (((sk_B @ sk_C) = (sk_A))),
% 0.23/0.55      inference('sup-', [status(thm)], ['22', '33'])).
% 0.23/0.55  thf('35', plain,
% 0.23/0.55      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.23/0.55      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.23/0.55  thf(l1_zfmisc_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.23/0.55  thf('36', plain,
% 0.23/0.55      (![X51 : $i, X53 : $i]:
% 0.23/0.55         ((r1_tarski @ (k1_tarski @ X51) @ X53) | ~ (r2_hidden @ X51 @ X53))),
% 0.23/0.55      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.23/0.55  thf('37', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((X0) = (k1_xboole_0)) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.23/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.23/0.55  thf(t12_xboole_1, axiom,
% 0.23/0.55    (![A:$i,B:$i]:
% 0.23/0.55     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.23/0.55  thf('38', plain,
% 0.23/0.55      (![X7 : $i, X8 : $i]:
% 0.23/0.55         (((k2_xboole_0 @ X8 @ X7) = (X7)) | ~ (r1_tarski @ X8 @ X7))),
% 0.23/0.55      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.23/0.55  thf('39', plain,
% 0.23/0.55      (![X57 : $i, X58 : $i]:
% 0.23/0.55         ((k3_tarski @ (k2_tarski @ X57 @ X58)) = (k2_xboole_0 @ X57 @ X58))),
% 0.23/0.55      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.23/0.55  thf('40', plain,
% 0.23/0.55      (![X7 : $i, X8 : $i]:
% 0.23/0.55         (((k3_tarski @ (k2_tarski @ X8 @ X7)) = (X7))
% 0.23/0.55          | ~ (r1_tarski @ X8 @ X7))),
% 0.23/0.55      inference('demod', [status(thm)], ['38', '39'])).
% 0.23/0.55  thf('41', plain,
% 0.23/0.55      (![X0 : $i]:
% 0.23/0.55         (((X0) = (k1_xboole_0))
% 0.23/0.55          | ((k3_tarski @ (k2_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0)) = (X0)))),
% 0.23/0.55      inference('sup-', [status(thm)], ['37', '40'])).
% 0.23/0.55  thf('42', plain,
% 0.23/0.55      ((((k3_tarski @ (k2_tarski @ (k1_tarski @ sk_A) @ sk_C)) = (sk_C))
% 0.23/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.23/0.55      inference('sup+', [status(thm)], ['34', '41'])).
% 0.23/0.55  thf('43', plain, (((sk_B_1) = (k1_tarski @ sk_A))),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.23/0.55  thf('44', plain,
% 0.23/0.55      ((((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C)) = (sk_C))
% 0.23/0.55        | ((sk_C) = (k1_xboole_0)))),
% 0.23/0.55      inference('demod', [status(thm)], ['42', '43'])).
% 0.23/0.55  thf('45', plain, (((sk_C) != (k1_xboole_0))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('46', plain, (((k3_tarski @ (k2_tarski @ sk_B_1 @ sk_C)) = (sk_C))),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.23/0.55  thf('47', plain, (((sk_B_1) = (sk_C))),
% 0.23/0.55      inference('sup+', [status(thm)], ['12', '46'])).
% 0.23/0.55  thf('48', plain, (((sk_B_1) != (sk_C))),
% 0.23/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.55  thf('49', plain, ($false),
% 0.23/0.55      inference('simplify_reflect-', [status(thm)], ['47', '48'])).
% 0.23/0.55  
% 0.23/0.55  % SZS output end Refutation
% 0.23/0.55  
% 0.23/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
