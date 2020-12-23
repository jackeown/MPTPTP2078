%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hL437AkoWr

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 131 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  475 ( 936 expanded)
%              Number of equality atoms :   44 (  93 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t144_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C )
        & ( C
         != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r2_hidden @ A @ C )
          & ~ ( r2_hidden @ B @ C )
          & ( C
           != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t144_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('1',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( r2_hidden @ X23 @ X24 )
      | ( r1_xboole_0 @ ( k2_tarski @ X23 @ X25 ) @ X24 )
      | ( r2_hidden @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_tarski @ X2 @ X1 ) )
        = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('22',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('36',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ ( k4_xboole_0 @ X10 @ X11 ) )
      = ( k3_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['34','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ ( k2_tarski @ X2 @ X1 ) )
        = X0 )
      | ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','44'])).

thf('46',plain,(
    sk_C_1
 != ( k4_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( sk_C_1 != sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r2_hidden @ sk_B_1 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r2_hidden @ sk_B_1 @ sk_C_1 ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hL437AkoWr
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:31:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.59  % Solved by: fo/fo7.sh
% 0.22/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.59  % done 323 iterations in 0.131s
% 0.22/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.59  % SZS output start Refutation
% 0.22/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.59  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.59  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.59  thf(t144_zfmisc_1, conjecture,
% 0.22/0.59    (![A:$i,B:$i,C:$i]:
% 0.22/0.59     ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.22/0.59          ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ))).
% 0.22/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.59        ( ~( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) & 
% 0.22/0.59             ( ( C ) != ( k4_xboole_0 @ C @ ( k2_tarski @ A @ B ) ) ) ) ) )),
% 0.22/0.59    inference('cnf.neg', [status(esa)], [t144_zfmisc_1])).
% 0.22/0.59  thf('0', plain, (~ (r2_hidden @ sk_B_1 @ sk_C_1)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf(t57_zfmisc_1, axiom,
% 0.22/0.59    (![A:$i,B:$i,C:$i]:
% 0.22/0.59     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.22/0.59          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.22/0.59  thf('1', plain,
% 0.22/0.59      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.59         ((r2_hidden @ X23 @ X24)
% 0.22/0.59          | (r1_xboole_0 @ (k2_tarski @ X23 @ X25) @ X24)
% 0.22/0.59          | (r2_hidden @ X25 @ X24))),
% 0.22/0.59      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.22/0.59  thf(t7_xboole_0, axiom,
% 0.22/0.59    (![A:$i]:
% 0.22/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.59          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.59  thf('2', plain,
% 0.22/0.59      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.22/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.59  thf(t4_xboole_0, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.59  thf('3', plain,
% 0.22/0.59      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.22/0.59         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.22/0.59          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.22/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.59  thf('4', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.59  thf('5', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.59         ((r2_hidden @ X1 @ X0)
% 0.22/0.59          | (r2_hidden @ X2 @ X0)
% 0.22/0.59          | ((k3_xboole_0 @ (k2_tarski @ X2 @ X1) @ X0) = (k1_xboole_0)))),
% 0.22/0.59      inference('sup-', [status(thm)], ['1', '4'])).
% 0.22/0.59  thf(commutativity_k3_xboole_0, axiom,
% 0.22/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.22/0.59  thf('6', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.59  thf(t100_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.59  thf('7', plain,
% 0.22/0.59      (![X8 : $i, X9 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X8 @ X9)
% 0.22/0.59           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.59  thf('8', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X0 @ X1)
% 0.22/0.59           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.59  thf('9', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.59         (((k4_xboole_0 @ X0 @ (k2_tarski @ X2 @ X1))
% 0.22/0.59            = (k5_xboole_0 @ X0 @ k1_xboole_0))
% 0.22/0.59          | (r2_hidden @ X2 @ X0)
% 0.22/0.59          | (r2_hidden @ X1 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['5', '8'])).
% 0.22/0.59  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.59  thf('10', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.59  thf('11', plain,
% 0.22/0.59      (![X8 : $i, X9 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X8 @ X9)
% 0.22/0.59           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.59  thf('12', plain,
% 0.22/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['10', '11'])).
% 0.22/0.59  thf(t48_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]:
% 0.22/0.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.59  thf('13', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.59           = (k3_xboole_0 @ X10 @ X11))),
% 0.22/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.59  thf('14', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))
% 0.22/0.59           = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['12', '13'])).
% 0.22/0.59  thf('15', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.59  thf('16', plain,
% 0.22/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.59  thf(t79_xboole_1, axiom,
% 0.22/0.59    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.22/0.59  thf('17', plain,
% 0.22/0.59      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.22/0.59      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.22/0.59  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['16', '17'])).
% 0.22/0.59  thf('19', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.59  thf('20', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.59  thf('21', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.59           = (k3_xboole_0 @ X10 @ X11))),
% 0.22/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.59  thf('22', plain,
% 0.22/0.59      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.22/0.59      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.22/0.59  thf('23', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['21', '22'])).
% 0.22/0.59  thf('24', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         (r1_xboole_0 @ k1_xboole_0 @ 
% 0.22/0.59          (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['20', '23'])).
% 0.22/0.59  thf('25', plain,
% 0.22/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.59  thf('26', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.22/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.59  thf('27', plain,
% 0.22/0.59      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 0.22/0.59      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.59  thf('28', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.22/0.59  thf('29', plain,
% 0.22/0.59      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.22/0.59         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.22/0.59          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.22/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.59  thf('30', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.59          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.59  thf('31', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['27', '30'])).
% 0.22/0.59  thf('32', plain,
% 0.22/0.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['26', '31'])).
% 0.22/0.59  thf('33', plain,
% 0.22/0.59      (![X8 : $i, X9 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X8 @ X9)
% 0.22/0.59           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.22/0.59      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.59  thf('34', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['32', '33'])).
% 0.22/0.59  thf('35', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k3_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.22/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.59  thf('36', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.59           = (k3_xboole_0 @ X10 @ X11))),
% 0.22/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.59  thf('37', plain,
% 0.22/0.59      (![X10 : $i, X11 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X10 @ (k4_xboole_0 @ X10 @ X11))
% 0.22/0.59           = (k3_xboole_0 @ X10 @ X11))),
% 0.22/0.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.22/0.59  thf('38', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.59           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.22/0.59      inference('sup+', [status(thm)], ['36', '37'])).
% 0.22/0.59  thf('39', plain,
% 0.22/0.59      (![X0 : $i]:
% 0.22/0.59         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 0.22/0.59           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0))))),
% 0.22/0.59      inference('sup+', [status(thm)], ['35', '38'])).
% 0.22/0.59  thf('40', plain,
% 0.22/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ (k5_xboole_0 @ X0 @ X0)) = (X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.59  thf('41', plain,
% 0.22/0.59      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['39', '40'])).
% 0.22/0.59  thf('42', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.22/0.59      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.59  thf('43', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['41', '42'])).
% 0.22/0.59  thf('44', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.22/0.59      inference('sup+', [status(thm)], ['34', '43'])).
% 0.22/0.59  thf('45', plain,
% 0.22/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.59         (((k4_xboole_0 @ X0 @ (k2_tarski @ X2 @ X1)) = (X0))
% 0.22/0.59          | (r2_hidden @ X2 @ X0)
% 0.22/0.59          | (r2_hidden @ X1 @ X0))),
% 0.22/0.59      inference('demod', [status(thm)], ['9', '44'])).
% 0.22/0.59  thf('46', plain,
% 0.22/0.59      (((sk_C_1) != (k4_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B_1)))),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('47', plain,
% 0.22/0.59      ((((sk_C_1) != (sk_C_1))
% 0.22/0.59        | (r2_hidden @ sk_B_1 @ sk_C_1)
% 0.22/0.59        | (r2_hidden @ sk_A @ sk_C_1))),
% 0.22/0.59      inference('sup-', [status(thm)], ['45', '46'])).
% 0.22/0.59  thf('48', plain,
% 0.22/0.59      (((r2_hidden @ sk_A @ sk_C_1) | (r2_hidden @ sk_B_1 @ sk_C_1))),
% 0.22/0.59      inference('simplify', [status(thm)], ['47'])).
% 0.22/0.59  thf('49', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.22/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.59  thf('50', plain, ((r2_hidden @ sk_B_1 @ sk_C_1)),
% 0.22/0.59      inference('clc', [status(thm)], ['48', '49'])).
% 0.22/0.59  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 0.22/0.59  
% 0.22/0.59  % SZS output end Refutation
% 0.22/0.59  
% 0.22/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
