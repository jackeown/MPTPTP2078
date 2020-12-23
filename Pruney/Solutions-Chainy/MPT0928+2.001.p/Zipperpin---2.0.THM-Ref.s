%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wmEHX9HLvT

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:20 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   59 (  80 expanded)
%              Number of leaves         :   17 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  470 ( 823 expanded)
%              Number of equality atoms :   10 (  16 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t88_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_tarski @ E @ F )
        & ( r1_tarski @ G @ H ) )
     => ( r1_tarski @ ( k4_zfmisc_1 @ A @ C @ E @ G ) @ ( k4_zfmisc_1 @ B @ D @ F @ H ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
        ( ( ( r1_tarski @ A @ B )
          & ( r1_tarski @ C @ D )
          & ( r1_tarski @ E @ F )
          & ( r1_tarski @ G @ H ) )
       => ( r1_tarski @ ( k4_zfmisc_1 @ A @ C @ E @ G ) @ ( k4_zfmisc_1 @ B @ D @ F @ H ) ) ) ),
    inference('cnf.neg',[status(esa)],[t88_mcart_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ sk_G ) @ ( k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ sk_H ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k4_zfmisc_1 @ A @ B @ C @ D )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('2',plain,(
    r1_tarski @ sk_G @ sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t118_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) )
        & ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X5 @ X3 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_G ) @ ( k2_zfmisc_1 @ X0 @ sk_H ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_G ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) @ sk_H ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_G ) @ ( k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('9',plain,(
    r1_tarski @ sk_E @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X5 @ X3 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_E ) @ ( k2_zfmisc_1 @ X0 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_E ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ sk_F ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_E ) @ ( k3_zfmisc_1 @ X1 @ X0 @ sk_F ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X5 @ X3 ) @ ( k2_zfmisc_1 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_C ) @ ( k2_zfmisc_1 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_A @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ ( k2_zfmisc_1 @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) @ X0 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('27',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( k3_zfmisc_1 @ X6 @ X7 @ X8 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_C @ X0 ) @ ( k3_zfmisc_1 @ sk_B @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k3_zfmisc_1 @ sk_B @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k3_zfmisc_1 @ sk_A @ sk_C @ sk_E ) @ ( k3_zfmisc_1 @ sk_B @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['14','30'])).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ ( k2_zfmisc_1 @ X3 @ X5 ) @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t118_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_A @ sk_C @ sk_E ) @ X0 ) @ ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ sk_B @ sk_D @ sk_F ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('35',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12 )
      = ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ X9 @ X10 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_zfmisc_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ X0 ) @ ( k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ sk_G ) @ ( k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ sk_H ) ),
    inference('sup-',[status(thm)],['7','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wmEHX9HLvT
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:53:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.60/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.81  % Solved by: fo/fo7.sh
% 0.60/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.81  % done 793 iterations in 0.364s
% 0.60/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.81  % SZS output start Refutation
% 0.60/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.81  thf(sk_H_type, type, sk_H: $i).
% 0.60/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.81  thf(sk_G_type, type, sk_G: $i).
% 0.60/0.81  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.60/0.81  thf(sk_F_type, type, sk_F: $i).
% 0.60/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.81  thf(sk_E_type, type, sk_E: $i).
% 0.60/0.81  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.81  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.60/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.81  thf(t88_mcart_1, conjecture,
% 0.60/0.81    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.60/0.81     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.60/0.81         ( r1_tarski @ E @ F ) & ( r1_tarski @ G @ H ) ) =>
% 0.60/0.81       ( r1_tarski @
% 0.60/0.81         ( k4_zfmisc_1 @ A @ C @ E @ G ) @ ( k4_zfmisc_1 @ B @ D @ F @ H ) ) ))).
% 0.60/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.81    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.60/0.81        ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.60/0.81            ( r1_tarski @ E @ F ) & ( r1_tarski @ G @ H ) ) =>
% 0.60/0.81          ( r1_tarski @
% 0.60/0.81            ( k4_zfmisc_1 @ A @ C @ E @ G ) @ ( k4_zfmisc_1 @ B @ D @ F @ H ) ) ) )),
% 0.60/0.81    inference('cnf.neg', [status(esa)], [t88_mcart_1])).
% 0.60/0.81  thf('0', plain,
% 0.60/0.81      (~ (r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ sk_G) @ 
% 0.60/0.81          (k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ sk_H))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(d4_zfmisc_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.81     ( ( k4_zfmisc_1 @ A @ B @ C @ D ) =
% 0.60/0.81       ( k2_zfmisc_1 @ ( k3_zfmisc_1 @ A @ B @ C ) @ D ) ))).
% 0.60/0.81  thf('1', plain,
% 0.60/0.81      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.81         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 0.60/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 0.60/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.60/0.81  thf('2', plain, ((r1_tarski @ sk_G @ sk_H)),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(t118_zfmisc_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( r1_tarski @ A @ B ) =>
% 0.60/0.81       ( ( r1_tarski @ ( k2_zfmisc_1 @ A @ C ) @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.60/0.81         ( r1_tarski @ ( k2_zfmisc_1 @ C @ A ) @ ( k2_zfmisc_1 @ C @ B ) ) ) ))).
% 0.60/0.81  thf('3', plain,
% 0.60/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X3 @ X4)
% 0.60/0.81          | (r1_tarski @ (k2_zfmisc_1 @ X5 @ X3) @ (k2_zfmisc_1 @ X5 @ X4)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.60/0.81  thf('4', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_G) @ (k2_zfmisc_1 @ X0 @ sk_H))),
% 0.60/0.81      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.81  thf('5', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.81         (r1_tarski @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_G) @ 
% 0.60/0.81          (k2_zfmisc_1 @ (k3_zfmisc_1 @ X2 @ X1 @ X0) @ sk_H))),
% 0.60/0.81      inference('sup+', [status(thm)], ['1', '4'])).
% 0.60/0.81  thf('6', plain,
% 0.60/0.81      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.81         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 0.60/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 0.60/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.60/0.81  thf('7', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.81         (r1_tarski @ (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_G) @ 
% 0.60/0.81          (k4_zfmisc_1 @ X2 @ X1 @ X0 @ sk_H))),
% 0.60/0.81      inference('demod', [status(thm)], ['5', '6'])).
% 0.60/0.81  thf(d3_zfmisc_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.60/0.81       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.60/0.81  thf('8', plain,
% 0.60/0.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.60/0.81         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.60/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.60/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.60/0.81  thf('9', plain, ((r1_tarski @ sk_E @ sk_F)),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('10', plain,
% 0.60/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X3 @ X4)
% 0.60/0.81          | (r1_tarski @ (k2_zfmisc_1 @ X5 @ X3) @ (k2_zfmisc_1 @ X5 @ X4)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.60/0.81  thf('11', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_E) @ (k2_zfmisc_1 @ X0 @ sk_F))),
% 0.60/0.81      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.81  thf('12', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (r1_tarski @ (k3_zfmisc_1 @ X1 @ X0 @ sk_E) @ 
% 0.60/0.81          (k2_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X0) @ sk_F))),
% 0.60/0.81      inference('sup+', [status(thm)], ['8', '11'])).
% 0.60/0.81  thf('13', plain,
% 0.60/0.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.60/0.81         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.60/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.60/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.60/0.81  thf('14', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         (r1_tarski @ (k3_zfmisc_1 @ X1 @ X0 @ sk_E) @ 
% 0.60/0.81          (k3_zfmisc_1 @ X1 @ X0 @ sk_F))),
% 0.60/0.81      inference('demod', [status(thm)], ['12', '13'])).
% 0.60/0.81  thf('15', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('16', plain,
% 0.60/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X3 @ X4)
% 0.60/0.81          | (r1_tarski @ (k2_zfmisc_1 @ X5 @ X3) @ (k2_zfmisc_1 @ X5 @ X4)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.60/0.81  thf('17', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_C) @ (k2_zfmisc_1 @ X0 @ sk_D))),
% 0.60/0.81      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.81  thf('18', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('19', plain,
% 0.60/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X3 @ X4)
% 0.60/0.81          | (r1_tarski @ (k2_zfmisc_1 @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.60/0.81  thf('20', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ (k2_zfmisc_1 @ sk_B @ X0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['18', '19'])).
% 0.60/0.81  thf(t1_xboole_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.60/0.81       ( r1_tarski @ A @ C ) ))).
% 0.60/0.81  thf('21', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X0 @ X1)
% 0.60/0.81          | ~ (r1_tarski @ X1 @ X2)
% 0.60/0.81          | (r1_tarski @ X0 @ X2))),
% 0.60/0.81      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.60/0.81  thf('22', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ X0) @ X1)
% 0.60/0.81          | ~ (r1_tarski @ (k2_zfmisc_1 @ sk_B @ X0) @ X1))),
% 0.60/0.81      inference('sup-', [status(thm)], ['20', '21'])).
% 0.60/0.81  thf('23', plain,
% 0.60/0.81      ((r1_tarski @ (k2_zfmisc_1 @ sk_A @ sk_C) @ (k2_zfmisc_1 @ sk_B @ sk_D))),
% 0.60/0.81      inference('sup-', [status(thm)], ['17', '22'])).
% 0.60/0.81  thf('24', plain,
% 0.60/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X3 @ X4)
% 0.60/0.81          | (r1_tarski @ (k2_zfmisc_1 @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.60/0.81  thf('25', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (r1_tarski @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C) @ X0) @ 
% 0.60/0.81          (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_D) @ X0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.81  thf('26', plain,
% 0.60/0.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.60/0.81         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.60/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.60/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.60/0.81  thf('27', plain,
% 0.60/0.81      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.60/0.81         ((k3_zfmisc_1 @ X6 @ X7 @ X8)
% 0.60/0.81           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7) @ X8))),
% 0.60/0.81      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.60/0.81  thf('28', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (r1_tarski @ (k3_zfmisc_1 @ sk_A @ sk_C @ X0) @ 
% 0.60/0.81          (k3_zfmisc_1 @ sk_B @ sk_D @ X0))),
% 0.60/0.81      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.60/0.81  thf('29', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X0 @ X1)
% 0.60/0.81          | ~ (r1_tarski @ X1 @ X2)
% 0.60/0.81          | (r1_tarski @ X0 @ X2))),
% 0.60/0.81      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.60/0.81  thf('30', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((r1_tarski @ (k3_zfmisc_1 @ sk_A @ sk_C @ X0) @ X1)
% 0.60/0.81          | ~ (r1_tarski @ (k3_zfmisc_1 @ sk_B @ sk_D @ X0) @ X1))),
% 0.60/0.81      inference('sup-', [status(thm)], ['28', '29'])).
% 0.60/0.81  thf('31', plain,
% 0.60/0.81      ((r1_tarski @ (k3_zfmisc_1 @ sk_A @ sk_C @ sk_E) @ 
% 0.60/0.81        (k3_zfmisc_1 @ sk_B @ sk_D @ sk_F))),
% 0.60/0.81      inference('sup-', [status(thm)], ['14', '30'])).
% 0.60/0.81  thf('32', plain,
% 0.60/0.81      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X3 @ X4)
% 0.60/0.81          | (r1_tarski @ (k2_zfmisc_1 @ X3 @ X5) @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.60/0.81      inference('cnf', [status(esa)], [t118_zfmisc_1])).
% 0.60/0.81  thf('33', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (r1_tarski @ 
% 0.60/0.81          (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_A @ sk_C @ sk_E) @ X0) @ 
% 0.60/0.81          (k2_zfmisc_1 @ (k3_zfmisc_1 @ sk_B @ sk_D @ sk_F) @ X0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.81  thf('34', plain,
% 0.60/0.81      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.81         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 0.60/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 0.60/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.60/0.81  thf('35', plain,
% 0.60/0.81      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.81         ((k4_zfmisc_1 @ X9 @ X10 @ X11 @ X12)
% 0.60/0.81           = (k2_zfmisc_1 @ (k3_zfmisc_1 @ X9 @ X10 @ X11) @ X12))),
% 0.60/0.81      inference('cnf', [status(esa)], [d4_zfmisc_1])).
% 0.60/0.81  thf('36', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         (r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ X0) @ 
% 0.60/0.81          (k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ X0))),
% 0.60/0.81      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.60/0.81  thf('37', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.81         (~ (r1_tarski @ X0 @ X1)
% 0.60/0.81          | ~ (r1_tarski @ X1 @ X2)
% 0.60/0.81          | (r1_tarski @ X0 @ X2))),
% 0.60/0.81      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.60/0.81  thf('38', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ X0) @ X1)
% 0.60/0.81          | ~ (r1_tarski @ (k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ X0) @ X1))),
% 0.60/0.81      inference('sup-', [status(thm)], ['36', '37'])).
% 0.60/0.81  thf('39', plain,
% 0.60/0.81      ((r1_tarski @ (k4_zfmisc_1 @ sk_A @ sk_C @ sk_E @ sk_G) @ 
% 0.60/0.81        (k4_zfmisc_1 @ sk_B @ sk_D @ sk_F @ sk_H))),
% 0.60/0.81      inference('sup-', [status(thm)], ['7', '38'])).
% 0.60/0.81  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.60/0.81  
% 0.60/0.81  % SZS output end Refutation
% 0.60/0.81  
% 0.60/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
