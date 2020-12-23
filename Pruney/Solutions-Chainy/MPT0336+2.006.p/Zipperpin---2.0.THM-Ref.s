%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qk2NTut0Kj

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:20 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 100 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  470 ( 780 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X16 @ X17 )
      | ( r2_hidden @ ( sk_C @ X17 @ X16 ) @ ( k3_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X39 ) @ X40 )
      | ( r2_hidden @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_xboole_0 @ X16 @ X19 ) )
      | ~ ( r1_xboole_0 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('22',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_xboole_0 @ X25 @ X26 )
      | ( r1_xboole_0 @ X25 @ ( k3_xboole_0 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21','26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('30',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('32',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k3_xboole_0 @ X16 @ X19 ) )
      | ~ ( r1_xboole_0 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('36',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('39',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('41',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_xboole_0 @ X28 @ X29 )
      | ( ( k3_xboole_0 @ X28 @ ( k2_xboole_0 @ X29 @ X30 ) )
        = ( k3_xboole_0 @ X28 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k3_xboole_0 @ X10 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['2','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qk2NTut0Kj
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.51/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.72  % Solved by: fo/fo7.sh
% 0.51/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.72  % done 599 iterations in 0.273s
% 0.51/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.72  % SZS output start Refutation
% 0.51/0.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.51/0.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.51/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.51/0.72  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.51/0.72  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.51/0.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.51/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.72  thf(t149_zfmisc_1, conjecture,
% 0.51/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.72     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.51/0.72         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.51/0.72       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.51/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.72    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.51/0.72        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.51/0.72            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.51/0.72          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.51/0.72    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.51/0.72  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(commutativity_k2_xboole_0, axiom,
% 0.51/0.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.51/0.72  thf('1', plain,
% 0.51/0.72      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.51/0.72      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.51/0.72  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.51/0.72      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.72  thf(t4_xboole_0, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.72            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.51/0.72       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.51/0.72            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.51/0.72  thf('3', plain,
% 0.51/0.72      (![X16 : $i, X17 : $i]:
% 0.51/0.72         ((r1_xboole_0 @ X16 @ X17)
% 0.51/0.72          | (r2_hidden @ (sk_C @ X17 @ X16) @ (k3_xboole_0 @ X16 @ X17)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.51/0.72  thf(l27_zfmisc_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.51/0.72  thf('4', plain,
% 0.51/0.72      (![X39 : $i, X40 : $i]:
% 0.51/0.72         ((r1_xboole_0 @ (k1_tarski @ X39) @ X40) | (r2_hidden @ X39 @ X40))),
% 0.51/0.72      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.51/0.72  thf('5', plain,
% 0.51/0.72      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(commutativity_k3_xboole_0, axiom,
% 0.51/0.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.51/0.72  thf('6', plain,
% 0.51/0.72      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.51/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.72  thf('7', plain,
% 0.51/0.72      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.51/0.72      inference('demod', [status(thm)], ['5', '6'])).
% 0.51/0.72  thf(t28_xboole_1, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.51/0.72  thf('8', plain,
% 0.51/0.72      (![X22 : $i, X23 : $i]:
% 0.51/0.72         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 0.51/0.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.51/0.72  thf('9', plain,
% 0.51/0.72      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))
% 0.51/0.72         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.51/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.72  thf('10', plain,
% 0.51/0.72      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.51/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.72  thf('11', plain,
% 0.51/0.72      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.51/0.72         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.51/0.72      inference('demod', [status(thm)], ['9', '10'])).
% 0.51/0.72  thf('12', plain,
% 0.51/0.72      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.51/0.72         (~ (r2_hidden @ X18 @ (k3_xboole_0 @ X16 @ X19))
% 0.51/0.72          | ~ (r1_xboole_0 @ X16 @ X19))),
% 0.51/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.51/0.72  thf('13', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.51/0.72          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.51/0.72  thf('14', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.51/0.72          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['4', '13'])).
% 0.51/0.72  thf('15', plain,
% 0.51/0.72      (((r1_xboole_0 @ sk_B @ sk_A)
% 0.51/0.72        | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['3', '14'])).
% 0.51/0.72  thf('16', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(d4_xboole_0, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i]:
% 0.51/0.72     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.51/0.72       ( ![D:$i]:
% 0.51/0.72         ( ( r2_hidden @ D @ C ) <=>
% 0.51/0.72           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.51/0.72  thf('17', plain,
% 0.51/0.72      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.51/0.72         (~ (r2_hidden @ X4 @ X5)
% 0.51/0.72          | ~ (r2_hidden @ X4 @ X6)
% 0.51/0.72          | (r2_hidden @ X4 @ X7)
% 0.51/0.72          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.51/0.72      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.51/0.72  thf('18', plain,
% 0.51/0.72      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.51/0.72         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 0.51/0.72          | ~ (r2_hidden @ X4 @ X6)
% 0.51/0.72          | ~ (r2_hidden @ X4 @ X5))),
% 0.51/0.72      inference('simplify', [status(thm)], ['17'])).
% 0.51/0.72  thf('19', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (r2_hidden @ sk_D_1 @ X0)
% 0.51/0.72          | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ X0 @ sk_C_1)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['16', '18'])).
% 0.51/0.72  thf('20', plain,
% 0.51/0.72      (((r1_xboole_0 @ sk_B @ sk_A)
% 0.51/0.72        | (r2_hidden @ sk_D_1 @ 
% 0.51/0.72           (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C_1)))),
% 0.51/0.72      inference('sup-', [status(thm)], ['15', '19'])).
% 0.51/0.72  thf('21', plain,
% 0.51/0.72      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.51/0.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.51/0.72  thf('22', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(t74_xboole_1, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i]:
% 0.51/0.72     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.51/0.72          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.51/0.72  thf('23', plain,
% 0.51/0.72      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.51/0.72         (~ (r1_xboole_0 @ X25 @ X26)
% 0.51/0.72          | (r1_xboole_0 @ X25 @ (k3_xboole_0 @ X26 @ X27)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.51/0.72  thf('24', plain,
% 0.51/0.72      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['22', '23'])).
% 0.51/0.72  thf(d7_xboole_0, axiom,
% 0.51/0.72    (![A:$i,B:$i]:
% 0.51/0.72     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.51/0.72       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.51/0.72  thf('25', plain,
% 0.51/0.72      (![X10 : $i, X11 : $i]:
% 0.51/0.72         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 0.51/0.72          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.51/0.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.51/0.72  thf('26', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.72  thf('27', plain,
% 0.51/0.72      (((r1_xboole_0 @ sk_B @ sk_A) | (r2_hidden @ sk_D_1 @ k1_xboole_0))),
% 0.51/0.72      inference('demod', [status(thm)], ['20', '21', '26'])).
% 0.51/0.72  thf('28', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.51/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.72  thf(symmetry_r1_xboole_0, axiom,
% 0.51/0.72    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.51/0.72  thf('29', plain,
% 0.51/0.72      (![X14 : $i, X15 : $i]:
% 0.51/0.72         ((r1_xboole_0 @ X14 @ X15) | ~ (r1_xboole_0 @ X15 @ X14))),
% 0.51/0.72      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.51/0.72  thf('30', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.51/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.72  thf('31', plain,
% 0.51/0.72      (![X10 : $i, X11 : $i]:
% 0.51/0.72         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 0.51/0.72          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.51/0.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.51/0.72  thf('32', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['30', '31'])).
% 0.51/0.72  thf('33', plain,
% 0.51/0.72      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.51/0.72         (~ (r2_hidden @ X18 @ (k3_xboole_0 @ X16 @ X19))
% 0.51/0.72          | ~ (r1_xboole_0 @ X16 @ X19))),
% 0.51/0.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.51/0.72  thf('34', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.51/0.72      inference('sup-', [status(thm)], ['32', '33'])).
% 0.51/0.72  thf('35', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.51/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.72  thf('36', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.51/0.72      inference('demod', [status(thm)], ['34', '35'])).
% 0.51/0.72  thf('37', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.51/0.72      inference('clc', [status(thm)], ['27', '36'])).
% 0.51/0.72  thf('38', plain,
% 0.51/0.72      (![X10 : $i, X11 : $i]:
% 0.51/0.72         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 0.51/0.72          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.51/0.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.51/0.72  thf('39', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['37', '38'])).
% 0.51/0.72  thf('40', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.51/0.72      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.72  thf(t78_xboole_1, axiom,
% 0.51/0.72    (![A:$i,B:$i,C:$i]:
% 0.51/0.72     ( ( r1_xboole_0 @ A @ B ) =>
% 0.51/0.72       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.51/0.72         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.51/0.72  thf('41', plain,
% 0.51/0.72      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.51/0.72         (~ (r1_xboole_0 @ X28 @ X29)
% 0.51/0.72          | ((k3_xboole_0 @ X28 @ (k2_xboole_0 @ X29 @ X30))
% 0.51/0.72              = (k3_xboole_0 @ X28 @ X30)))),
% 0.51/0.72      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.51/0.72  thf('42', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0))
% 0.51/0.72           = (k3_xboole_0 @ sk_B @ X0))),
% 0.51/0.72      inference('sup-', [status(thm)], ['40', '41'])).
% 0.51/0.72  thf('43', plain,
% 0.51/0.72      (![X10 : $i, X12 : $i]:
% 0.51/0.72         ((r1_xboole_0 @ X10 @ X12)
% 0.51/0.72          | ((k3_xboole_0 @ X10 @ X12) != (k1_xboole_0)))),
% 0.51/0.72      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.51/0.72  thf('44', plain,
% 0.51/0.72      (![X0 : $i]:
% 0.51/0.72         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 0.51/0.73          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['42', '43'])).
% 0.51/0.73  thf('45', plain,
% 0.51/0.73      ((((k1_xboole_0) != (k1_xboole_0))
% 0.51/0.73        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.51/0.73      inference('sup-', [status(thm)], ['39', '44'])).
% 0.51/0.73  thf('46', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.51/0.73      inference('simplify', [status(thm)], ['45'])).
% 0.51/0.73  thf('47', plain,
% 0.51/0.73      (![X14 : $i, X15 : $i]:
% 0.51/0.73         ((r1_xboole_0 @ X14 @ X15) | ~ (r1_xboole_0 @ X15 @ X14))),
% 0.51/0.73      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.51/0.73  thf('48', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.51/0.73      inference('sup-', [status(thm)], ['46', '47'])).
% 0.51/0.73  thf('49', plain, ($false), inference('demod', [status(thm)], ['2', '48'])).
% 0.51/0.73  
% 0.51/0.73  % SZS output end Refutation
% 0.51/0.73  
% 0.51/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
