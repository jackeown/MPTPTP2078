%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WpPspS80Ri

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:01 EST 2020

% Result     : Theorem 7.11s
% Output     : Refutation 7.11s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 106 expanded)
%              Number of leaves         :   19 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :  429 ( 889 expanded)
%              Number of equality atoms :   21 (  64 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t143_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
        & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) )
          & ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) )
       => ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t120_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) )
      & ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C )
        = ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ( ( k2_zfmisc_1 @ X13 @ ( k2_xboole_0 @ X10 @ X12 ) )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X13 @ X10 ) @ ( k2_zfmisc_1 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('2',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X8 @ X9 ) )
      = ( k2_xboole_0 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    r1_tarski @ sk_B @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('10',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t13_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X2 ) @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('14',plain,(
    ! [X4: $i] :
      ( ( k2_xboole_0 @ X4 @ k1_xboole_0 )
      = X4 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X2 @ ( k2_xboole_0 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ),
    inference('sup+',[status(thm)],['8','17'])).

thf('19',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ X10 @ X12 ) @ X11 )
      = ( k2_xboole_0 @ ( k2_zfmisc_1 @ X10 @ X11 ) @ ( k2_zfmisc_1 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t120_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('21',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    r1_tarski @ sk_A @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X1 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ X0 @ ( k2_zfmisc_1 @ sk_C @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['20','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_D ) ) ),
    inference('sup+',[status(thm)],['19','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X3 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ ( k2_xboole_0 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t13_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ sk_A @ X2 ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X0 @ sk_C ) @ sk_D ) @ X1 ) )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_xboole_0 @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ X1 @ sk_C ) @ sk_D ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ X0 ) @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['18','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_E @ sk_C ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['1','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('36',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_A @ sk_B ) @ ( k2_zfmisc_1 @ ( k2_xboole_0 @ sk_C @ sk_E ) @ ( k2_xboole_0 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WpPspS80Ri
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:54:32 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.11/7.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.11/7.32  % Solved by: fo/fo7.sh
% 7.11/7.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.11/7.32  % done 6016 iterations in 6.859s
% 7.11/7.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.11/7.32  % SZS output start Refutation
% 7.11/7.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.11/7.32  thf(sk_B_type, type, sk_B: $i).
% 7.11/7.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.11/7.32  thf(sk_C_type, type, sk_C: $i).
% 7.11/7.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.11/7.32  thf(sk_A_type, type, sk_A: $i).
% 7.11/7.32  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 7.11/7.32  thf(sk_F_type, type, sk_F: $i).
% 7.11/7.32  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 7.11/7.32  thf(sk_E_type, type, sk_E: $i).
% 7.11/7.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.11/7.32  thf(sk_D_type, type, sk_D: $i).
% 7.11/7.32  thf(t143_zfmisc_1, conjecture,
% 7.11/7.32    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.11/7.32     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 7.11/7.32         ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 7.11/7.32       ( r1_tarski @
% 7.11/7.32         ( k2_xboole_0 @ A @ B ) @ 
% 7.11/7.32         ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ))).
% 7.11/7.32  thf(zf_stmt_0, negated_conjecture,
% 7.11/7.32    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.11/7.32        ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ C @ D ) ) & 
% 7.11/7.32            ( r1_tarski @ B @ ( k2_zfmisc_1 @ E @ F ) ) ) =>
% 7.11/7.32          ( r1_tarski @
% 7.11/7.32            ( k2_xboole_0 @ A @ B ) @ 
% 7.11/7.32            ( k2_zfmisc_1 @ ( k2_xboole_0 @ C @ E ) @ ( k2_xboole_0 @ D @ F ) ) ) ) )),
% 7.11/7.32    inference('cnf.neg', [status(esa)], [t143_zfmisc_1])).
% 7.11/7.32  thf('0', plain,
% 7.11/7.32      (~ (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 7.11/7.32          (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 7.11/7.32           (k2_xboole_0 @ sk_D @ sk_F)))),
% 7.11/7.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.11/7.32  thf(t120_zfmisc_1, axiom,
% 7.11/7.32    (![A:$i,B:$i,C:$i]:
% 7.11/7.32     ( ( ( k2_zfmisc_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 7.11/7.32         ( k2_xboole_0 @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 7.11/7.32       ( ( k2_zfmisc_1 @ ( k2_xboole_0 @ A @ B ) @ C ) =
% 7.11/7.32         ( k2_xboole_0 @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 7.11/7.32  thf('1', plain,
% 7.11/7.32      (![X10 : $i, X12 : $i, X13 : $i]:
% 7.11/7.32         ((k2_zfmisc_1 @ X13 @ (k2_xboole_0 @ X10 @ X12))
% 7.11/7.32           = (k2_xboole_0 @ (k2_zfmisc_1 @ X13 @ X10) @ 
% 7.11/7.32              (k2_zfmisc_1 @ X13 @ X12)))),
% 7.11/7.32      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 7.11/7.32  thf('2', plain,
% 7.11/7.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 7.11/7.32         ((k2_zfmisc_1 @ (k2_xboole_0 @ X10 @ X12) @ X11)
% 7.11/7.32           = (k2_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 7.11/7.32              (k2_zfmisc_1 @ X12 @ X11)))),
% 7.11/7.32      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 7.11/7.32  thf(commutativity_k2_tarski, axiom,
% 7.11/7.32    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 7.11/7.32  thf('3', plain,
% 7.11/7.32      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 7.11/7.32      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 7.11/7.32  thf(l51_zfmisc_1, axiom,
% 7.11/7.32    (![A:$i,B:$i]:
% 7.11/7.32     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 7.11/7.32  thf('4', plain,
% 7.11/7.32      (![X8 : $i, X9 : $i]:
% 7.11/7.32         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 7.11/7.32      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 7.11/7.32  thf('5', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i]:
% 7.11/7.32         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 7.11/7.32      inference('sup+', [status(thm)], ['3', '4'])).
% 7.11/7.32  thf('6', plain,
% 7.11/7.32      (![X8 : $i, X9 : $i]:
% 7.11/7.32         ((k3_tarski @ (k2_tarski @ X8 @ X9)) = (k2_xboole_0 @ X8 @ X9))),
% 7.11/7.32      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 7.11/7.32  thf('7', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.11/7.32      inference('sup+', [status(thm)], ['5', '6'])).
% 7.11/7.32  thf('8', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.11/7.32         ((k2_zfmisc_1 @ (k2_xboole_0 @ X2 @ X1) @ X0)
% 7.11/7.32           = (k2_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0) @ (k2_zfmisc_1 @ X2 @ X0)))),
% 7.11/7.32      inference('sup+', [status(thm)], ['2', '7'])).
% 7.11/7.32  thf('9', plain, ((r1_tarski @ sk_B @ (k2_zfmisc_1 @ sk_E @ sk_F))),
% 7.11/7.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.11/7.32  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 7.11/7.32  thf('10', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 7.11/7.32      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.11/7.32  thf(t13_xboole_1, axiom,
% 7.11/7.32    (![A:$i,B:$i,C:$i,D:$i]:
% 7.11/7.32     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) ) =>
% 7.11/7.32       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ D ) ) ))).
% 7.11/7.32  thf('11', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.11/7.32         (~ (r1_tarski @ X0 @ X1)
% 7.11/7.32          | ~ (r1_tarski @ X2 @ X3)
% 7.11/7.32          | (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X3)))),
% 7.11/7.32      inference('cnf', [status(esa)], [t13_xboole_1])).
% 7.11/7.32  thf('12', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.11/7.32         ((r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X2) @ 
% 7.11/7.32           (k2_xboole_0 @ X0 @ X1))
% 7.11/7.32          | ~ (r1_tarski @ X2 @ X1))),
% 7.11/7.32      inference('sup-', [status(thm)], ['10', '11'])).
% 7.11/7.32  thf('13', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.11/7.32      inference('sup+', [status(thm)], ['5', '6'])).
% 7.11/7.32  thf(t1_boole, axiom,
% 7.11/7.32    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 7.11/7.32  thf('14', plain, (![X4 : $i]: ((k2_xboole_0 @ X4 @ k1_xboole_0) = (X4))),
% 7.11/7.32      inference('cnf', [status(esa)], [t1_boole])).
% 7.11/7.32  thf('15', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 7.11/7.32      inference('sup+', [status(thm)], ['13', '14'])).
% 7.11/7.32  thf('16', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.11/7.32         ((r1_tarski @ X2 @ (k2_xboole_0 @ X0 @ X1)) | ~ (r1_tarski @ X2 @ X1))),
% 7.11/7.32      inference('demod', [status(thm)], ['12', '15'])).
% 7.11/7.32  thf('17', plain,
% 7.11/7.32      (![X0 : $i]:
% 7.11/7.32         (r1_tarski @ sk_B @ (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_E @ sk_F)))),
% 7.11/7.32      inference('sup-', [status(thm)], ['9', '16'])).
% 7.11/7.32  thf('18', plain,
% 7.11/7.32      (![X0 : $i]:
% 7.11/7.32         (r1_tarski @ sk_B @ (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F))),
% 7.11/7.32      inference('sup+', [status(thm)], ['8', '17'])).
% 7.11/7.32  thf('19', plain,
% 7.11/7.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 7.11/7.32         ((k2_zfmisc_1 @ (k2_xboole_0 @ X10 @ X12) @ X11)
% 7.11/7.32           = (k2_xboole_0 @ (k2_zfmisc_1 @ X10 @ X11) @ 
% 7.11/7.32              (k2_zfmisc_1 @ X12 @ X11)))),
% 7.11/7.32      inference('cnf', [status(esa)], [t120_zfmisc_1])).
% 7.11/7.32  thf('20', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.11/7.32      inference('sup+', [status(thm)], ['5', '6'])).
% 7.11/7.32  thf('21', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 7.11/7.32      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.11/7.32  thf('22', plain, ((r1_tarski @ sk_A @ (k2_zfmisc_1 @ sk_C @ sk_D))),
% 7.11/7.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.11/7.32  thf('23', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.11/7.32         (~ (r1_tarski @ X0 @ X1)
% 7.11/7.32          | ~ (r1_tarski @ X2 @ X3)
% 7.11/7.32          | (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X3)))),
% 7.11/7.32      inference('cnf', [status(esa)], [t13_xboole_1])).
% 7.11/7.32  thf('24', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i]:
% 7.11/7.32         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X1) @ 
% 7.11/7.32           (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0))
% 7.11/7.32          | ~ (r1_tarski @ X1 @ X0))),
% 7.11/7.32      inference('sup-', [status(thm)], ['22', '23'])).
% 7.11/7.32  thf('25', plain,
% 7.11/7.32      (![X0 : $i]:
% 7.11/7.32         (r1_tarski @ (k2_xboole_0 @ sk_A @ k1_xboole_0) @ 
% 7.11/7.32          (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0))),
% 7.11/7.32      inference('sup-', [status(thm)], ['21', '24'])).
% 7.11/7.32  thf('26', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.11/7.32      inference('sup+', [status(thm)], ['5', '6'])).
% 7.11/7.32  thf('27', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 7.11/7.32      inference('sup+', [status(thm)], ['13', '14'])).
% 7.11/7.32  thf('28', plain,
% 7.11/7.32      (![X0 : $i]:
% 7.11/7.32         (r1_tarski @ sk_A @ (k2_xboole_0 @ (k2_zfmisc_1 @ sk_C @ sk_D) @ X0))),
% 7.11/7.32      inference('demod', [status(thm)], ['25', '26', '27'])).
% 7.11/7.32  thf('29', plain,
% 7.11/7.32      (![X0 : $i]:
% 7.11/7.32         (r1_tarski @ sk_A @ (k2_xboole_0 @ X0 @ (k2_zfmisc_1 @ sk_C @ sk_D)))),
% 7.11/7.32      inference('sup+', [status(thm)], ['20', '28'])).
% 7.11/7.32  thf('30', plain,
% 7.11/7.32      (![X0 : $i]:
% 7.11/7.32         (r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C) @ sk_D))),
% 7.11/7.32      inference('sup+', [status(thm)], ['19', '29'])).
% 7.11/7.32  thf('31', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.11/7.32         (~ (r1_tarski @ X0 @ X1)
% 7.11/7.32          | ~ (r1_tarski @ X2 @ X3)
% 7.11/7.32          | (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ (k2_xboole_0 @ X1 @ X3)))),
% 7.11/7.32      inference('cnf', [status(esa)], [t13_xboole_1])).
% 7.11/7.32  thf('32', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.11/7.32         ((r1_tarski @ (k2_xboole_0 @ sk_A @ X2) @ 
% 7.11/7.32           (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X0 @ sk_C) @ sk_D) @ X1))
% 7.11/7.32          | ~ (r1_tarski @ X2 @ X1))),
% 7.11/7.32      inference('sup-', [status(thm)], ['30', '31'])).
% 7.11/7.32  thf('33', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i]:
% 7.11/7.32         (r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 7.11/7.32          (k2_xboole_0 @ (k2_zfmisc_1 @ (k2_xboole_0 @ X1 @ sk_C) @ sk_D) @ 
% 7.11/7.32           (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ X0) @ sk_F)))),
% 7.11/7.32      inference('sup-', [status(thm)], ['18', '32'])).
% 7.11/7.32  thf('34', plain,
% 7.11/7.32      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 7.11/7.32        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_E @ sk_C) @ 
% 7.11/7.32         (k2_xboole_0 @ sk_D @ sk_F)))),
% 7.11/7.32      inference('sup+', [status(thm)], ['1', '33'])).
% 7.11/7.32  thf('35', plain,
% 7.11/7.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.11/7.32      inference('sup+', [status(thm)], ['5', '6'])).
% 7.11/7.32  thf('36', plain,
% 7.11/7.32      ((r1_tarski @ (k2_xboole_0 @ sk_A @ sk_B) @ 
% 7.11/7.32        (k2_zfmisc_1 @ (k2_xboole_0 @ sk_C @ sk_E) @ 
% 7.11/7.32         (k2_xboole_0 @ sk_D @ sk_F)))),
% 7.11/7.32      inference('demod', [status(thm)], ['34', '35'])).
% 7.11/7.32  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 7.11/7.32  
% 7.11/7.32  % SZS output end Refutation
% 7.11/7.32  
% 7.11/7.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
