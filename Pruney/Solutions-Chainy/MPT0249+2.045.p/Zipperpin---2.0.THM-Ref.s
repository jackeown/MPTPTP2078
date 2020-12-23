%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qyBo5PsKob

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:44 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 207 expanded)
%              Number of leaves         :   22 (  67 expanded)
%              Depth                    :   17
%              Number of atoms          :  444 (1786 expanded)
%              Number of equality atoms :   61 ( 344 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('0',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ X13 @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

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

thf('1',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X27
        = ( k1_tarski @ X26 ) )
      | ( X27 = k1_xboole_0 )
      | ~ ( r1_tarski @ X27 @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
      | ( X0 = k1_xboole_0 )
      | ( X0
        = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_B_1
      = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ( r2_hidden @ X4 @ X6 )
      | ( X6
       != ( k2_xboole_0 @ X7 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X7: $i] :
      ( ( r2_hidden @ X4 @ ( k2_xboole_0 @ X7 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('15',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r2_hidden @ ( sk_B @ sk_C_2 ) @ sk_B_1 ),
    inference('simplify_reflect-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( sk_B_1
    = ( k2_xboole_0 @ sk_B_1 @ sk_C_2 ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = sk_B_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X20: $i] :
      ( ( k2_tarski @ X20 @ X20 )
      = ( k1_tarski @ X20 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X29 @ X30 ) )
      = ( k2_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['23','29'])).

thf('31',plain,
    ( ( k3_tarski @ sk_B_1 )
    = sk_A ),
    inference('sup+',[status(thm)],['20','30'])).

thf('32',plain,
    ( ( k1_tarski @ ( k3_tarski @ sk_B_1 ) )
    = sk_B_1 ),
    inference(demod,[status(thm)],['19','31'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( X18 = X15 )
      | ( X17
       != ( k1_tarski @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('34',plain,(
    ! [X15: $i,X18: $i] :
      ( ( X18 = X15 )
      | ~ ( r2_hidden @ X18 @ ( k1_tarski @ X15 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( sk_B @ sk_C_2 )
    = ( k3_tarski @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','35'])).

thf('37',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('38',plain,
    ( ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    sk_C_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ ( k3_tarski @ sk_B_1 ) @ sk_C_2 ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ( X0
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ( ( sk_C @ X0 @ sk_B_1 )
        = ( k3_tarski @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 )
      | ( r1_tarski @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B_1 @ X0 )
      | ~ ( r2_hidden @ ( k3_tarski @ sk_B_1 ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    r1_tarski @ sk_B_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['40','46'])).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('49',plain,
    ( ( k2_xboole_0 @ sk_B_1 @ sk_C_2 )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    sk_B_1 = sk_C_2 ),
    inference('sup+',[status(thm)],['8','49'])).

thf('51',plain,(
    sk_B_1 != sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qyBo5PsKob
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 192 iterations in 0.110s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.36/0.56  thf(t7_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      (![X13 : $i, X14 : $i]: (r1_tarski @ X13 @ (k2_xboole_0 @ X13 @ X14))),
% 0.36/0.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.36/0.56  thf(t44_zfmisc_1, conjecture,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.36/0.56          ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.56          ( ( C ) != ( k1_xboole_0 ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.56        ( ~( ( ( k1_tarski @ A ) = ( k2_xboole_0 @ B @ C ) ) & 
% 0.36/0.56             ( ( B ) != ( C ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.36/0.56             ( ( C ) != ( k1_xboole_0 ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t44_zfmisc_1])).
% 0.36/0.56  thf('1', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(l3_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.36/0.56       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (![X26 : $i, X27 : $i]:
% 0.36/0.56         (((X27) = (k1_tarski @ X26))
% 0.36/0.56          | ((X27) = (k1_xboole_0))
% 0.36/0.56          | ~ (r1_tarski @ X27 @ (k1_tarski @ X26)))),
% 0.36/0.56      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.36/0.56  thf('3', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.36/0.56          | ((X0) = (k1_xboole_0))
% 0.36/0.56          | ((X0) = (k1_tarski @ sk_A)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.56  thf('4', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (~ (r1_tarski @ X0 @ (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.36/0.56          | ((X0) = (k1_xboole_0))
% 0.36/0.56          | ((X0) = (k2_xboole_0 @ sk_B_1 @ sk_C_2)))),
% 0.36/0.56      inference('demod', [status(thm)], ['3', '4'])).
% 0.36/0.56  thf('6', plain,
% 0.36/0.56      ((((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))
% 0.36/0.56        | ((sk_B_1) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['0', '5'])).
% 0.36/0.56  thf('7', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('8', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.36/0.56  thf('9', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.36/0.56  thf(t7_xboole_0, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.36/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (![X10 : $i]:
% 0.36/0.56         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.36/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.56  thf(d3_xboole_0, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.36/0.56       ( ![D:$i]:
% 0.36/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.56           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X4 @ X5)
% 0.36/0.56          | (r2_hidden @ X4 @ X6)
% 0.36/0.56          | ((X6) != (k2_xboole_0 @ X7 @ X5)))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      (![X4 : $i, X5 : $i, X7 : $i]:
% 0.36/0.56         ((r2_hidden @ X4 @ (k2_xboole_0 @ X7 @ X5)) | ~ (r2_hidden @ X4 @ X5))),
% 0.36/0.56      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.56  thf('13', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (((X0) = (k1_xboole_0))
% 0.36/0.56          | (r2_hidden @ (sk_B @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['10', '12'])).
% 0.36/0.56  thf('14', plain,
% 0.36/0.56      (((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1) | ((sk_C_2) = (k1_xboole_0)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['9', '13'])).
% 0.36/0.56  thf('15', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('16', plain, ((r2_hidden @ (sk_B @ sk_C_2) @ sk_B_1)),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['14', '15'])).
% 0.36/0.56  thf('17', plain, (((k1_tarski @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('18', plain, (((sk_B_1) = (k2_xboole_0 @ sk_B_1 @ sk_C_2))),
% 0.36/0.56      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.36/0.56  thf('19', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.36/0.56      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.56  thf('20', plain, (((k1_tarski @ sk_A) = (sk_B_1))),
% 0.36/0.56      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.56  thf(t69_enumset1, axiom,
% 0.36/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.36/0.56  thf('21', plain,
% 0.36/0.56      (![X20 : $i]: ((k2_tarski @ X20 @ X20) = (k1_tarski @ X20))),
% 0.36/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.36/0.56  thf(l51_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      (![X29 : $i, X30 : $i]:
% 0.36/0.56         ((k3_tarski @ (k2_tarski @ X29 @ X30)) = (k2_xboole_0 @ X29 @ X30))),
% 0.36/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.36/0.56      inference('sup+', [status(thm)], ['21', '22'])).
% 0.36/0.56  thf(d3_tarski, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      (![X1 : $i, X3 : $i]:
% 0.36/0.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      (![X1 : $i, X3 : $i]:
% 0.36/0.56         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('26', plain,
% 0.36/0.56      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.56  thf('27', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.36/0.56      inference('simplify', [status(thm)], ['26'])).
% 0.36/0.56  thf(t12_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      (![X11 : $i, X12 : $i]:
% 0.36/0.56         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.36/0.56      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.56  thf('29', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.36/0.56  thf('30', plain, (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (X0))),
% 0.36/0.56      inference('demod', [status(thm)], ['23', '29'])).
% 0.36/0.56  thf('31', plain, (((k3_tarski @ sk_B_1) = (sk_A))),
% 0.36/0.56      inference('sup+', [status(thm)], ['20', '30'])).
% 0.36/0.56  thf('32', plain, (((k1_tarski @ (k3_tarski @ sk_B_1)) = (sk_B_1))),
% 0.36/0.57      inference('demod', [status(thm)], ['19', '31'])).
% 0.36/0.57  thf(d1_tarski, axiom,
% 0.36/0.57    (![A:$i,B:$i]:
% 0.36/0.57     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.36/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.36/0.57  thf('33', plain,
% 0.36/0.57      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X18 @ X17)
% 0.36/0.57          | ((X18) = (X15))
% 0.36/0.57          | ((X17) != (k1_tarski @ X15)))),
% 0.36/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.36/0.57  thf('34', plain,
% 0.36/0.57      (![X15 : $i, X18 : $i]:
% 0.36/0.57         (((X18) = (X15)) | ~ (r2_hidden @ X18 @ (k1_tarski @ X15)))),
% 0.36/0.57      inference('simplify', [status(thm)], ['33'])).
% 0.36/0.57  thf('35', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (k3_tarski @ sk_B_1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['32', '34'])).
% 0.36/0.57  thf('36', plain, (((sk_B @ sk_C_2) = (k3_tarski @ sk_B_1))),
% 0.36/0.57      inference('sup-', [status(thm)], ['16', '35'])).
% 0.36/0.57  thf('37', plain,
% 0.36/0.57      (![X10 : $i]:
% 0.36/0.57         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 0.36/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.36/0.57  thf('38', plain,
% 0.36/0.57      (((r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_2)
% 0.36/0.57        | ((sk_C_2) = (k1_xboole_0)))),
% 0.36/0.57      inference('sup+', [status(thm)], ['36', '37'])).
% 0.36/0.57  thf('39', plain, (((sk_C_2) != (k1_xboole_0))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('40', plain, ((r2_hidden @ (k3_tarski @ sk_B_1) @ sk_C_2)),
% 0.36/0.57      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.36/0.57  thf('41', plain,
% 0.36/0.57      (![X1 : $i, X3 : $i]:
% 0.36/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.36/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.57  thf('42', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (r2_hidden @ X0 @ sk_B_1) | ((X0) = (k3_tarski @ sk_B_1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['32', '34'])).
% 0.36/0.57  thf('43', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((r1_tarski @ sk_B_1 @ X0)
% 0.36/0.57          | ((sk_C @ X0 @ sk_B_1) = (k3_tarski @ sk_B_1)))),
% 0.36/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.36/0.57  thf('44', plain,
% 0.36/0.57      (![X1 : $i, X3 : $i]:
% 0.36/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.36/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.57  thf('45', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         (~ (r2_hidden @ (k3_tarski @ sk_B_1) @ X0)
% 0.36/0.57          | (r1_tarski @ sk_B_1 @ X0)
% 0.36/0.57          | (r1_tarski @ sk_B_1 @ X0))),
% 0.36/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.36/0.57  thf('46', plain,
% 0.36/0.57      (![X0 : $i]:
% 0.36/0.57         ((r1_tarski @ sk_B_1 @ X0) | ~ (r2_hidden @ (k3_tarski @ sk_B_1) @ X0))),
% 0.36/0.57      inference('simplify', [status(thm)], ['45'])).
% 0.36/0.57  thf('47', plain, ((r1_tarski @ sk_B_1 @ sk_C_2)),
% 0.36/0.57      inference('sup-', [status(thm)], ['40', '46'])).
% 0.36/0.57  thf('48', plain,
% 0.36/0.57      (![X11 : $i, X12 : $i]:
% 0.36/0.57         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.36/0.57      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.36/0.57  thf('49', plain, (((k2_xboole_0 @ sk_B_1 @ sk_C_2) = (sk_C_2))),
% 0.36/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.36/0.57  thf('50', plain, (((sk_B_1) = (sk_C_2))),
% 0.36/0.57      inference('sup+', [status(thm)], ['8', '49'])).
% 0.36/0.57  thf('51', plain, (((sk_B_1) != (sk_C_2))),
% 0.36/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.57  thf('52', plain, ($false),
% 0.36/0.57      inference('simplify_reflect-', [status(thm)], ['50', '51'])).
% 0.36/0.57  
% 0.36/0.57  % SZS output end Refutation
% 0.36/0.57  
% 0.36/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
