%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.srqjM4Xs9R

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:25 EST 2020

% Result     : Theorem 0.99s
% Output     : Refutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :   73 (  95 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :   21
%              Number of atoms          :  463 ( 697 expanded)
%              Number of equality atoms :   40 (  53 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t149_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
        & ( r2_hidden @ D @ C )
        & ( r1_xboole_0 @ C @ B ) )
     => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) )
          & ( r2_hidden @ D @ C )
          & ( r1_xboole_0 @ C @ B ) )
       => ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t149_zfmisc_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('5',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('8',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('9',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X31
        = ( k1_tarski @ X30 ) )
      | ( X31 = k1_xboole_0 )
      | ~ ( r1_tarski @ X31 @ ( k1_tarski @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('10',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X9 @ X10 ) @ X9 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t77_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_xboole_0 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t77_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('17',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_C_1 )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('28',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ sk_D_1 @ ( k1_tarski @ sk_D_1 ) )
    | ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('32',plain,(
    ! [X24: $i] :
      ( ( k2_tarski @ X24 @ X24 )
      = ( k1_tarski @ X24 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('33',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ( r2_hidden @ X19 @ X20 )
      | ( X20
       != ( k2_tarski @ X21 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('34',plain,(
    ! [X18: $i,X21: $i] :
      ( r2_hidden @ X18 @ ( k2_tarski @ X21 @ X18 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','34'])).

thf('36',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('38',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['38'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_xboole_0 @ X15 @ X16 )
      | ( ( k3_xboole_0 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
        = ( k3_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','45'])).

thf('47',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['0','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.srqjM4Xs9R
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:24:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.99/1.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.99/1.16  % Solved by: fo/fo7.sh
% 0.99/1.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.99/1.16  % done 1772 iterations in 0.703s
% 0.99/1.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.99/1.16  % SZS output start Refutation
% 0.99/1.16  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.99/1.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.99/1.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.99/1.16  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.99/1.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.99/1.16  thf(sk_B_type, type, sk_B: $i).
% 0.99/1.16  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.99/1.16  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.99/1.16  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.99/1.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.99/1.16  thf(sk_A_type, type, sk_A: $i).
% 0.99/1.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.99/1.16  thf(t149_zfmisc_1, conjecture,
% 0.99/1.16    (![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.16     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.99/1.16         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.99/1.16       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.99/1.16  thf(zf_stmt_0, negated_conjecture,
% 0.99/1.16    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.99/1.16        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.99/1.16            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.99/1.16          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.99/1.16    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.99/1.16  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(d7_xboole_0, axiom,
% 0.99/1.16    (![A:$i,B:$i]:
% 0.99/1.16     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.99/1.16       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.99/1.16  thf('2', plain,
% 0.99/1.16      (![X2 : $i, X3 : $i]:
% 0.99/1.16         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.99/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.99/1.16  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 0.99/1.16      inference('sup-', [status(thm)], ['1', '2'])).
% 0.99/1.16  thf(commutativity_k3_xboole_0, axiom,
% 0.99/1.16    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.99/1.16  thf('4', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.16  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.99/1.16      inference('demod', [status(thm)], ['3', '4'])).
% 0.99/1.16  thf('6', plain,
% 0.99/1.16      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf('7', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.16  thf('8', plain,
% 0.99/1.16      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.99/1.16      inference('demod', [status(thm)], ['6', '7'])).
% 0.99/1.16  thf(l3_zfmisc_1, axiom,
% 0.99/1.16    (![A:$i,B:$i]:
% 0.99/1.16     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.99/1.16       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.99/1.16  thf('9', plain,
% 0.99/1.16      (![X30 : $i, X31 : $i]:
% 0.99/1.16         (((X31) = (k1_tarski @ X30))
% 0.99/1.16          | ((X31) = (k1_xboole_0))
% 0.99/1.16          | ~ (r1_tarski @ X31 @ (k1_tarski @ X30)))),
% 0.99/1.16      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.99/1.16  thf('10', plain,
% 0.99/1.16      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.99/1.16        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_tarski @ sk_D_1)))),
% 0.99/1.16      inference('sup-', [status(thm)], ['8', '9'])).
% 0.99/1.16  thf(t17_xboole_1, axiom,
% 0.99/1.16    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.99/1.16  thf('11', plain,
% 0.99/1.16      (![X9 : $i, X10 : $i]: (r1_tarski @ (k3_xboole_0 @ X9 @ X10) @ X9)),
% 0.99/1.16      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.99/1.16  thf('12', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.99/1.16      inference('demod', [status(thm)], ['3', '4'])).
% 0.99/1.16  thf('13', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.16  thf(t77_xboole_1, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i]:
% 0.99/1.16     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 0.99/1.16          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 0.99/1.16  thf('14', plain,
% 0.99/1.16      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.99/1.16         ((r1_xboole_0 @ X12 @ X13)
% 0.99/1.16          | ~ (r1_xboole_0 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 0.99/1.16          | ~ (r1_tarski @ X12 @ X14))),
% 0.99/1.16      inference('cnf', [status(esa)], [t77_xboole_1])).
% 0.99/1.16  thf('15', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.99/1.16         (~ (r1_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.99/1.16          | ~ (r1_tarski @ X2 @ X1)
% 0.99/1.16          | (r1_xboole_0 @ X2 @ X0))),
% 0.99/1.16      inference('sup-', [status(thm)], ['13', '14'])).
% 0.99/1.16  thf('16', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         (~ (r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.99/1.16          | (r1_xboole_0 @ X0 @ sk_C_1)
% 0.99/1.16          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.99/1.16      inference('sup-', [status(thm)], ['12', '15'])).
% 0.99/1.16  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.99/1.16  thf('17', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 0.99/1.16      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.99/1.16  thf('18', plain,
% 0.99/1.16      (![X0 : $i]: ((r1_xboole_0 @ X0 @ sk_C_1) | ~ (r1_tarski @ X0 @ sk_B))),
% 0.99/1.16      inference('demod', [status(thm)], ['16', '17'])).
% 0.99/1.16  thf('19', plain,
% 0.99/1.16      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_1)),
% 0.99/1.16      inference('sup-', [status(thm)], ['11', '18'])).
% 0.99/1.16  thf('20', plain,
% 0.99/1.16      (![X2 : $i, X3 : $i]:
% 0.99/1.16         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.99/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.99/1.16  thf('21', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_C_1) = (k1_xboole_0))),
% 0.99/1.16      inference('sup-', [status(thm)], ['19', '20'])).
% 0.99/1.16  thf('22', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.16  thf('23', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         ((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))),
% 0.99/1.16      inference('demod', [status(thm)], ['21', '22'])).
% 0.99/1.16  thf('24', plain,
% 0.99/1.16      (![X2 : $i, X4 : $i]:
% 0.99/1.16         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.99/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.99/1.16  thf('25', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         (((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.16          | (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0)))),
% 0.99/1.16      inference('sup-', [status(thm)], ['23', '24'])).
% 0.99/1.16  thf('26', plain,
% 0.99/1.16      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 0.99/1.16      inference('simplify', [status(thm)], ['25'])).
% 0.99/1.16  thf('27', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 0.99/1.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.99/1.16  thf(t3_xboole_0, axiom,
% 0.99/1.16    (![A:$i,B:$i]:
% 0.99/1.16     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.99/1.16            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.99/1.16       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.99/1.16            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.99/1.16  thf('28', plain,
% 0.99/1.16      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.99/1.16         (~ (r2_hidden @ X7 @ X5)
% 0.99/1.16          | ~ (r2_hidden @ X7 @ X8)
% 0.99/1.16          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.99/1.16      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.99/1.16  thf('29', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D_1 @ X0))),
% 0.99/1.16      inference('sup-', [status(thm)], ['27', '28'])).
% 0.99/1.16  thf('30', plain,
% 0.99/1.16      (![X0 : $i]: ~ (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 0.99/1.16      inference('sup-', [status(thm)], ['26', '29'])).
% 0.99/1.16  thf('31', plain,
% 0.99/1.16      ((~ (r2_hidden @ sk_D_1 @ (k1_tarski @ sk_D_1))
% 0.99/1.16        | ((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.99/1.16      inference('sup-', [status(thm)], ['10', '30'])).
% 0.99/1.16  thf(t69_enumset1, axiom,
% 0.99/1.16    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.99/1.16  thf('32', plain,
% 0.99/1.16      (![X24 : $i]: ((k2_tarski @ X24 @ X24) = (k1_tarski @ X24))),
% 0.99/1.16      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.99/1.16  thf(d2_tarski, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i]:
% 0.99/1.16     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.99/1.16       ( ![D:$i]:
% 0.99/1.16         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.99/1.16  thf('33', plain,
% 0.99/1.16      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.99/1.16         (((X19) != (X18))
% 0.99/1.16          | (r2_hidden @ X19 @ X20)
% 0.99/1.16          | ((X20) != (k2_tarski @ X21 @ X18)))),
% 0.99/1.16      inference('cnf', [status(esa)], [d2_tarski])).
% 0.99/1.16  thf('34', plain,
% 0.99/1.16      (![X18 : $i, X21 : $i]: (r2_hidden @ X18 @ (k2_tarski @ X21 @ X18))),
% 0.99/1.16      inference('simplify', [status(thm)], ['33'])).
% 0.99/1.16  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.99/1.16      inference('sup+', [status(thm)], ['32', '34'])).
% 0.99/1.16  thf('36', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.99/1.16      inference('demod', [status(thm)], ['31', '35'])).
% 0.99/1.16  thf('37', plain,
% 0.99/1.16      (![X2 : $i, X4 : $i]:
% 0.99/1.16         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.99/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.99/1.16  thf('38', plain,
% 0.99/1.16      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.99/1.16      inference('sup-', [status(thm)], ['36', '37'])).
% 0.99/1.16  thf('39', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.99/1.16      inference('simplify', [status(thm)], ['38'])).
% 0.99/1.16  thf(t78_xboole_1, axiom,
% 0.99/1.16    (![A:$i,B:$i,C:$i]:
% 0.99/1.16     ( ( r1_xboole_0 @ A @ B ) =>
% 0.99/1.16       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.99/1.16         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.99/1.16  thf('40', plain,
% 0.99/1.16      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.99/1.16         (~ (r1_xboole_0 @ X15 @ X16)
% 0.99/1.16          | ((k3_xboole_0 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.99/1.16              = (k3_xboole_0 @ X15 @ X17)))),
% 0.99/1.16      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.99/1.16  thf('41', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 0.99/1.16           = (k3_xboole_0 @ sk_B @ X0))),
% 0.99/1.16      inference('sup-', [status(thm)], ['39', '40'])).
% 0.99/1.16  thf('42', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.99/1.16      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.99/1.16  thf('43', plain,
% 0.99/1.16      (![X2 : $i, X4 : $i]:
% 0.99/1.16         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.99/1.16      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.99/1.16  thf('44', plain,
% 0.99/1.16      (![X0 : $i, X1 : $i]:
% 0.99/1.16         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 0.99/1.16      inference('sup-', [status(thm)], ['42', '43'])).
% 0.99/1.16  thf('45', plain,
% 0.99/1.16      (![X0 : $i]:
% 0.99/1.16         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 0.99/1.16          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 0.99/1.16      inference('sup-', [status(thm)], ['41', '44'])).
% 0.99/1.16  thf('46', plain,
% 0.99/1.16      ((((k1_xboole_0) != (k1_xboole_0))
% 0.99/1.16        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B))),
% 0.99/1.16      inference('sup-', [status(thm)], ['5', '45'])).
% 0.99/1.16  thf('47', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.99/1.16      inference('simplify', [status(thm)], ['46'])).
% 0.99/1.16  thf('48', plain, ($false), inference('demod', [status(thm)], ['0', '47'])).
% 0.99/1.16  
% 0.99/1.16  % SZS output end Refutation
% 0.99/1.16  
% 0.99/1.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
