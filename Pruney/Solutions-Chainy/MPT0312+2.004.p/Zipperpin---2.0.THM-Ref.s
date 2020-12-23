%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fx3MXTrFpE

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:35:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 108 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  508 ( 783 expanded)
%              Number of equality atoms :   60 (  93 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t124_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
        = ( k2_zfmisc_1 @ A @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D ) )
       => ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) )
          = ( k2_zfmisc_1 @ A @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t124_zfmisc_1])).

thf('0',plain,(
    ( k3_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ) )).

thf('1',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ X42 @ X44 ) @ ( k3_xboole_0 @ X43 @ X45 ) )
      = ( k3_xboole_0 @ ( k2_zfmisc_1 @ X42 @ X43 ) @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t123_zfmisc_1])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X10 @ X11 ) @ ( k2_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('21',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('24',plain,
    ( ( k5_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18','19','22','23'])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('28',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ sk_A @ ( k5_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = ( k5_xboole_0 @ sk_A @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_D )
    = sk_D ),
    inference('sup-',[status(thm)],['33','34'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_tarski @ X13 @ X12 )
      = ( k2_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t93_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X47 @ X48 ) )
      = ( k2_xboole_0 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k2_xboole_0 @ sk_D @ sk_C )
    = sk_D ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X10 @ X11 ) @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = ( k5_xboole_0 @ sk_D @ ( k5_xboole_0 @ sk_D @ sk_C ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('45',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X6 @ X7 ) @ X8 )
      = ( k5_xboole_0 @ X6 @ ( k5_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k3_xboole_0 @ sk_D @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    ( k2_zfmisc_1 @ sk_A @ sk_C )
 != ( k2_zfmisc_1 @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['0','1','32','49'])).

thf('51',plain,(
    $false ),
    inference(simplify,[status(thm)],['50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Fx3MXTrFpE
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:49:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 125 iterations in 0.059s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.51  thf(t124_zfmisc_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.21/0.51       ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.21/0.51         ( k2_zfmisc_1 @ A @ C ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 0.21/0.51          ( ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ D ) @ ( k2_zfmisc_1 @ B @ C ) ) =
% 0.21/0.51            ( k2_zfmisc_1 @ A @ C ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t124_zfmisc_1])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      (((k3_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_D) @ 
% 0.21/0.51         (k2_zfmisc_1 @ sk_B @ sk_C)) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t123_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( k2_zfmisc_1 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ D ) ) =
% 0.21/0.51       ( k3_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ D ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 0.21/0.51         ((k2_zfmisc_1 @ (k3_xboole_0 @ X42 @ X44) @ (k3_xboole_0 @ X43 @ X45))
% 0.21/0.51           = (k3_xboole_0 @ (k2_zfmisc_1 @ X42 @ X43) @ 
% 0.21/0.51              (k2_zfmisc_1 @ X44 @ X45)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t123_zfmisc_1])).
% 0.21/0.51  thf(t92_xboole_1, axiom,
% 0.21/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.51  thf('2', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.51  thf('3', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.51  thf('4', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t12_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.51  thf('6', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(t95_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k3_xboole_0 @ A @ B ) =
% 0.21/0.51       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X10 @ X11)
% 0.21/0.51           = (k5_xboole_0 @ (k5_xboole_0 @ X10 @ X11) @ 
% 0.21/0.51              (k2_xboole_0 @ X10 @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.21/0.51  thf(commutativity_k5_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X10 @ X11)
% 0.21/0.51           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 0.21/0.51              (k5_xboole_0 @ X10 @ X11)))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.21/0.51         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['6', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (((k3_xboole_0 @ sk_A @ sk_B)
% 0.21/0.51         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ sk_A)))),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '11'])).
% 0.21/0.51  thf(t91_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.21/0.51       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.21/0.51           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.21/0.51           = (k5_xboole_0 @ sk_B @ 
% 0.21/0.51              (k5_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_A) @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['12', '13'])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.21/0.51           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)
% 0.21/0.51           = (k5_xboole_0 @ sk_B @ 
% 0.21/0.51              (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0))))),
% 0.21/0.51      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.51         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ k1_xboole_0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['3', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.51  thf(t5_boole, axiom,
% 0.21/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.51  thf('21', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.51  thf('22', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (((k5_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18', '19', '22', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.21/0.51           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.51           = (k5_xboole_0 @ sk_A @ 
% 0.21/0.51              (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((X0)
% 0.21/0.51           = (k5_xboole_0 @ sk_A @ 
% 0.21/0.51              (k5_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (((k3_xboole_0 @ sk_A @ sk_B) = (k5_xboole_0 @ sk_A @ k1_xboole_0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['2', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.51  thf('31', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('32', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.51  thf('33', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X3 : $i, X4 : $i]:
% 0.21/0.51         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.21/0.51  thf('35', plain, (((k2_xboole_0 @ sk_C @ sk_D) = (sk_D))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf(commutativity_k2_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         ((k2_tarski @ X13 @ X12) = (k2_tarski @ X12 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.51  thf(t93_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('37', plain,
% 0.21/0.51      (![X47 : $i, X48 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.21/0.51      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X47 : $i, X48 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X47 @ X48)) = (k2_xboole_0 @ X47 @ X48))),
% 0.21/0.51      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain, (((k2_xboole_0 @ sk_D @ sk_C) = (sk_D))),
% 0.21/0.51      inference('demod', [status(thm)], ['35', '40'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X10 @ X11)
% 0.21/0.51           = (k5_xboole_0 @ (k2_xboole_0 @ X10 @ X11) @ 
% 0.21/0.51              (k5_xboole_0 @ X10 @ X11)))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8'])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (((k3_xboole_0 @ sk_D @ sk_C)
% 0.21/0.51         = (k5_xboole_0 @ sk_D @ (k5_xboole_0 @ sk_D @ sk_C)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.51  thf('44', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.51         ((k5_xboole_0 @ (k5_xboole_0 @ X6 @ X7) @ X8)
% 0.21/0.51           = (k5_xboole_0 @ X6 @ (k5_xboole_0 @ X7 @ X8)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.21/0.51           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['44', '45'])).
% 0.21/0.51  thf('47', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('48', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.51      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.51  thf('49', plain, (((k3_xboole_0 @ sk_D @ sk_C) = (sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['43', '48'])).
% 0.21/0.51  thf('50', plain,
% 0.21/0.51      (((k2_zfmisc_1 @ sk_A @ sk_C) != (k2_zfmisc_1 @ sk_A @ sk_C))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '1', '32', '49'])).
% 0.21/0.51  thf('51', plain, ($false), inference('simplify', [status(thm)], ['50'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
