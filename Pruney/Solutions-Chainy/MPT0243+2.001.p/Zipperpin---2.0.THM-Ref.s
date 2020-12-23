%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qph2gAHp2Y

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 177 expanded)
%              Number of leaves         :   14 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  373 (1478 expanded)
%              Number of equality atoms :    5 (  20 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t38_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k1_tarski @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r1_tarski @ ( k1_tarski @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['2','12','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['24'])).

thf('27',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','12','21','26'])).

thf('28',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('30',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['3'])).

thf('33',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['2','12','21','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(simpl_trail,[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X10 ) @ X12 )
      | ~ ( r2_hidden @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('36',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ sk_C )
      | ~ ( r1_tarski @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C ),
    inference('sup-',[status(thm)],['30','38'])).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('41',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['23','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qph2gAHp2Y
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 38 iterations in 0.016s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.48  thf(t38_zfmisc_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.48       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.48        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.20/0.48          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t38_zfmisc_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.20/0.48        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.20/0.48        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.48         <= (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.20/0.48       ~ ((r2_hidden @ sk_B @ sk_C)) | ~ ((r2_hidden @ sk_A @ sk_C))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ sk_C)
% 0.20/0.48        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.48         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf(t41_enumset1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( k2_tarski @ A @ B ) =
% 0.20/0.48       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         ((k2_tarski @ X8 @ X9)
% 0.20/0.48           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.48  thf(t11_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.20/0.48  thf('6', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.20/0.48      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.48          | (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C))
% 0.20/0.48         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.48  thf(l1_zfmisc_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         ((r2_hidden @ X10 @ X11) | ~ (r1_tarski @ (k1_tarski @ X10) @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ sk_C))
% 0.20/0.48         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.20/0.48       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.20/0.48         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf(commutativity_k2_tarski, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.48          | (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.20/0.48          | (r1_tarski @ (k1_tarski @ X0) @ X2))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_C))
% 0.20/0.48         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         ((r2_hidden @ X10 @ X11) | ~ (r1_tarski @ (k1_tarski @ X10) @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ sk_C))
% 0.20/0.48         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ sk_C)) | 
% 0.20/0.48       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf('22', plain, (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '12', '21'])).
% 0.20/0.48  thf('23', plain, (~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['1', '22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ sk_C)
% 0.20/0.48        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (((r2_hidden @ sk_B @ sk_C)) | 
% 0.20/0.48       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.48      inference('split', [status(esa)], ['24'])).
% 0.20/0.48  thf('27', plain, (((r2_hidden @ sk_B @ sk_C))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '12', '21', '26'])).
% 0.20/0.48  thf('28', plain, ((r2_hidden @ sk_B @ sk_C)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['25', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X10 : $i, X12 : $i]:
% 0.20/0.48         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.48  thf('30', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.20/0.48       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.20/0.48      inference('split', [status(esa)], ['3'])).
% 0.20/0.48  thf('33', plain, (((r2_hidden @ sk_A @ sk_C))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '12', '21', '32'])).
% 0.20/0.48  thf('34', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['31', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      (![X10 : $i, X12 : $i]:
% 0.20/0.48         ((r1_tarski @ (k1_tarski @ X10) @ X12) | ~ (r2_hidden @ X10 @ X12))),
% 0.20/0.48      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.48  thf('36', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.48  thf(t8_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.20/0.48       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.20/0.48  thf('37', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.48         (~ (r1_tarski @ X3 @ X4)
% 0.20/0.48          | ~ (r1_tarski @ X5 @ X4)
% 0.20/0.48          | (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.20/0.48      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ sk_C)
% 0.20/0.48          | ~ (r1_tarski @ X0 @ sk_C))),
% 0.20/0.48      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 0.20/0.48        sk_C)),
% 0.20/0.48      inference('sup-', [status(thm)], ['30', '38'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      (![X8 : $i, X9 : $i]:
% 0.20/0.48         ((k2_tarski @ X8 @ X9)
% 0.20/0.48           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.20/0.48      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.20/0.48  thf('41', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.20/0.48      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.48  thf('42', plain, ($false), inference('demod', [status(thm)], ['23', '41'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
