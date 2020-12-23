%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q0U8t8dRHG

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:16 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 115 expanded)
%              Number of leaves         :   18 (  42 expanded)
%              Depth                    :   15
%              Number of atoms          :  503 ( 894 expanded)
%              Number of equality atoms :   60 ( 107 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t148_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( ( k3_xboole_0 @ B @ C )
          = ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ A ) )
     => ( ( k3_xboole_0 @ A @ C )
        = ( k1_tarski @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( ( k3_xboole_0 @ B @ C )
            = ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ A ) )
       => ( ( k3_xboole_0 @ A @ C )
          = ( k1_tarski @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t148_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','10'])).

thf('12',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_C @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference('sup+',[status(thm)],['0','11'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('13',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25
        = ( k1_tarski @ X24 ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ sk_C @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_C @ sk_A )
      = ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ( k3_xboole_0 @ sk_A @ sk_C )
 != ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ( k3_xboole_0 @ sk_C @ sk_A )
 != ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_A )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C )
    = ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A )
    = ( k3_xboole_0 @ sk_B @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('25',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X25
        = ( k1_tarski @ X24 ) )
      | ( X25 = k1_xboole_0 )
      | ~ ( r1_tarski @ X25 @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ ( k1_tarski @ X26 ) )
      | ( X25 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('28',plain,(
    ! [X26: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X26 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X5 @ X6 ) @ X7 )
      = ( k3_xboole_0 @ X5 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X1 )
        = ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) ) )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 ) )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('39',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('40',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('42',plain,
    ( ( k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_D ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['22','23','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('49',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_A ),
    inference(simplify,[status(thm)],['51'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('53',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X22 ) @ X23 )
      | ~ ( r2_hidden @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('54',plain,(
    ~ ( r2_hidden @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Q0U8t8dRHG
% 0.16/0.35  % Computer   : n006.cluster.edu
% 0.16/0.35  % Model      : x86_64 x86_64
% 0.16/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.35  % Memory     : 8042.1875MB
% 0.16/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.35  % CPULimit   : 60
% 0.16/0.35  % DateTime   : Tue Dec  1 15:29:53 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.36  % Running in FO mode
% 0.77/0.96  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.96  % Solved by: fo/fo7.sh
% 0.77/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.96  % done 867 iterations in 0.491s
% 0.77/0.96  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.96  % SZS output start Refutation
% 0.77/0.96  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.77/0.96  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.77/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.96  thf(sk_D_type, type, sk_D: $i).
% 0.77/0.96  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.77/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.96  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.77/0.96  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.96  thf(t148_zfmisc_1, conjecture,
% 0.77/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.96     ( ( ( r1_tarski @ A @ B ) & 
% 0.77/0.96         ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.77/0.96         ( r2_hidden @ D @ A ) ) =>
% 0.77/0.96       ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ))).
% 0.77/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.96    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.77/0.96        ( ( ( r1_tarski @ A @ B ) & 
% 0.77/0.96            ( ( k3_xboole_0 @ B @ C ) = ( k1_tarski @ D ) ) & 
% 0.77/0.96            ( r2_hidden @ D @ A ) ) =>
% 0.77/0.96          ( ( k3_xboole_0 @ A @ C ) = ( k1_tarski @ D ) ) ) )),
% 0.77/0.96    inference('cnf.neg', [status(esa)], [t148_zfmisc_1])).
% 0.77/0.96  thf('0', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(commutativity_k3_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.77/0.96  thf('1', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf(t28_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.77/0.96  thf('3', plain,
% 0.77/0.96      (![X10 : $i, X11 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.77/0.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.96  thf('4', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.96  thf('5', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('6', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.77/0.96      inference('demod', [status(thm)], ['4', '5'])).
% 0.77/0.96  thf(t16_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i,C:$i]:
% 0.77/0.96     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.77/0.96       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.77/0.96  thf('7', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.77/0.96           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.77/0.96  thf(t17_xboole_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.77/0.96  thf('8', plain,
% 0.77/0.96      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.77/0.96      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.77/0.96  thf('9', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.77/0.96         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 0.77/0.96          (k3_xboole_0 @ X2 @ X1))),
% 0.77/0.96      inference('sup+', [status(thm)], ['7', '8'])).
% 0.77/0.96  thf('10', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ X0 @ sk_B))),
% 0.77/0.96      inference('sup+', [status(thm)], ['6', '9'])).
% 0.77/0.96  thf('11', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['1', '10'])).
% 0.77/0.96  thf('12', plain,
% 0.77/0.96      ((r1_tarski @ (k3_xboole_0 @ sk_C @ sk_A) @ (k1_tarski @ sk_D))),
% 0.77/0.96      inference('sup+', [status(thm)], ['0', '11'])).
% 0.77/0.96  thf(l3_zfmisc_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.77/0.96       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.77/0.96  thf('13', plain,
% 0.77/0.96      (![X24 : $i, X25 : $i]:
% 0.77/0.96         (((X25) = (k1_tarski @ X24))
% 0.77/0.96          | ((X25) = (k1_xboole_0))
% 0.77/0.96          | ~ (r1_tarski @ X25 @ (k1_tarski @ X24)))),
% 0.77/0.96      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.77/0.96  thf('14', plain,
% 0.77/0.96      ((((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))
% 0.77/0.96        | ((k3_xboole_0 @ sk_C @ sk_A) = (k1_tarski @ sk_D)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['12', '13'])).
% 0.77/0.96  thf('15', plain, (((k3_xboole_0 @ sk_A @ sk_C) != (k1_tarski @ sk_D))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('16', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('17', plain, (((k3_xboole_0 @ sk_C @ sk_A) != (k1_tarski @ sk_D))),
% 0.77/0.96      inference('demod', [status(thm)], ['15', '16'])).
% 0.77/0.96  thf('18', plain, (((k3_xboole_0 @ sk_C @ sk_A) = (k1_xboole_0))),
% 0.77/0.96      inference('simplify_reflect-', [status(thm)], ['14', '17'])).
% 0.77/0.96  thf('19', plain, (((k3_xboole_0 @ sk_B @ sk_C) = (k1_tarski @ sk_D))),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('20', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.77/0.96           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.77/0.96  thf('21', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ (k1_tarski @ sk_D) @ X0)
% 0.77/0.96           = (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['19', '20'])).
% 0.77/0.96  thf('22', plain,
% 0.77/0.96      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_A)
% 0.77/0.96         = (k3_xboole_0 @ sk_B @ k1_xboole_0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['18', '21'])).
% 0.77/0.96  thf('23', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('24', plain,
% 0.77/0.96      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.77/0.96      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.77/0.96  thf('25', plain,
% 0.77/0.96      (![X24 : $i, X25 : $i]:
% 0.77/0.96         (((X25) = (k1_tarski @ X24))
% 0.77/0.96          | ((X25) = (k1_xboole_0))
% 0.77/0.96          | ~ (r1_tarski @ X25 @ (k1_tarski @ X24)))),
% 0.77/0.96      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.77/0.96  thf('26', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0))
% 0.77/0.96          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.77/0.96      inference('sup-', [status(thm)], ['24', '25'])).
% 0.77/0.96  thf('27', plain,
% 0.77/0.96      (![X25 : $i, X26 : $i]:
% 0.77/0.96         ((r1_tarski @ X25 @ (k1_tarski @ X26)) | ((X25) != (k1_xboole_0)))),
% 0.77/0.96      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.77/0.96  thf('28', plain,
% 0.77/0.96      (![X26 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X26))),
% 0.77/0.96      inference('simplify', [status(thm)], ['27'])).
% 0.77/0.96  thf('29', plain,
% 0.77/0.96      (![X10 : $i, X11 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.77/0.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.96  thf('30', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['28', '29'])).
% 0.77/0.96  thf('31', plain,
% 0.77/0.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ (k3_xboole_0 @ X5 @ X6) @ X7)
% 0.77/0.96           = (k3_xboole_0 @ X5 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.77/0.96      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.77/0.96  thf('32', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.77/0.96           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['30', '31'])).
% 0.77/0.96  thf('33', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ k1_xboole_0 @ X1)
% 0.77/0.96            = (k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)))
% 0.77/0.96          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['26', '32'])).
% 0.77/0.96  thf('34', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['28', '29'])).
% 0.77/0.96  thf('35', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ k1_xboole_0 @ X1) = (k1_xboole_0))
% 0.77/0.96          | ((k3_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_xboole_0)))),
% 0.77/0.96      inference('demod', [status(thm)], ['33', '34'])).
% 0.77/0.96  thf('36', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.77/0.96           = (k3_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ X1) @ X0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['30', '31'])).
% 0.77/0.96  thf('37', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.77/0.96            = (k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0))
% 0.77/0.96          | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.77/0.96      inference('sup+', [status(thm)], ['35', '36'])).
% 0.77/0.96  thf('38', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         ((k3_xboole_0 @ k1_xboole_0 @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['28', '29'])).
% 0.77/0.96  thf('39', plain,
% 0.77/0.96      (![X8 : $i, X9 : $i]: (r1_tarski @ (k3_xboole_0 @ X8 @ X9) @ X8)),
% 0.77/0.96      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.77/0.96  thf('40', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 0.77/0.96      inference('sup+', [status(thm)], ['38', '39'])).
% 0.77/0.96  thf('41', plain,
% 0.77/0.96      (![X10 : $i, X11 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.77/0.96      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.77/0.96  thf('42', plain,
% 0.77/0.96      (((k3_xboole_0 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.96      inference('sup-', [status(thm)], ['40', '41'])).
% 0.77/0.96  thf('43', plain,
% 0.77/0.96      (![X0 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.77/0.96          | ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.77/0.96      inference('demod', [status(thm)], ['37', '42'])).
% 0.77/0.96  thf('44', plain,
% 0.77/0.96      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.77/0.96      inference('simplify', [status(thm)], ['43'])).
% 0.77/0.96  thf('45', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf('46', plain,
% 0.77/0.96      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.77/0.96      inference('sup+', [status(thm)], ['44', '45'])).
% 0.77/0.96  thf('47', plain,
% 0.77/0.96      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_D)) = (k1_xboole_0))),
% 0.77/0.96      inference('demod', [status(thm)], ['22', '23', '46'])).
% 0.77/0.96  thf('48', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.77/0.96  thf(d7_xboole_0, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.77/0.96       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.77/0.96  thf('49', plain,
% 0.77/0.96      (![X2 : $i, X4 : $i]:
% 0.77/0.96         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.77/0.96      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.77/0.96  thf('50', plain,
% 0.77/0.96      (![X0 : $i, X1 : $i]:
% 0.77/0.96         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.77/0.96      inference('sup-', [status(thm)], ['48', '49'])).
% 0.77/0.96  thf('51', plain,
% 0.77/0.96      ((((k1_xboole_0) != (k1_xboole_0))
% 0.77/0.96        | (r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_A))),
% 0.77/0.96      inference('sup-', [status(thm)], ['47', '50'])).
% 0.77/0.96  thf('52', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_A)),
% 0.77/0.96      inference('simplify', [status(thm)], ['51'])).
% 0.77/0.96  thf(l24_zfmisc_1, axiom,
% 0.77/0.96    (![A:$i,B:$i]:
% 0.77/0.96     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.77/0.96  thf('53', plain,
% 0.77/0.96      (![X22 : $i, X23 : $i]:
% 0.77/0.96         (~ (r1_xboole_0 @ (k1_tarski @ X22) @ X23) | ~ (r2_hidden @ X22 @ X23))),
% 0.77/0.96      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.77/0.96  thf('54', plain, (~ (r2_hidden @ sk_D @ sk_A)),
% 0.77/0.96      inference('sup-', [status(thm)], ['52', '53'])).
% 0.77/0.96  thf('55', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.77/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.96  thf('56', plain, ($false), inference('demod', [status(thm)], ['54', '55'])).
% 0.77/0.96  
% 0.77/0.96  % SZS output end Refutation
% 0.77/0.96  
% 0.77/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
