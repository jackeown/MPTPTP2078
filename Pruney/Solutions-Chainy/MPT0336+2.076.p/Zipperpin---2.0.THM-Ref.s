%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rcaNjDlp61

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:30 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   62 (  79 expanded)
%              Number of leaves         :   20 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  392 ( 648 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('7',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k3_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_tarski @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('17',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ( r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
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

thf('25',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['18','27'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ X18 @ X19 )
      | ( r1_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ ( k1_tarski @ sk_D ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['4','33'])).

thf('35',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','36'])).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('39',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference(demod,[status(thm)],['0','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rcaNjDlp61
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:47:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.90  % Solved by: fo/fo7.sh
% 0.68/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.90  % done 932 iterations in 0.467s
% 0.68/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.90  % SZS output start Refutation
% 0.68/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.90  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.68/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.68/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.68/0.90  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.68/0.90  thf(t149_zfmisc_1, conjecture,
% 0.68/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.90     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.68/0.90         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.68/0.90       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.68/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.68/0.90        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.68/0.90            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.68/0.90          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.68/0.90    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.68/0.90  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(symmetry_r1_xboole_0, axiom,
% 0.68/0.90    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.68/0.90  thf('2', plain,
% 0.68/0.90      (![X2 : $i, X3 : $i]:
% 0.68/0.90         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.68/0.90      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.68/0.90  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 0.68/0.90      inference('sup-', [status(thm)], ['1', '2'])).
% 0.68/0.90  thf(t4_xboole_0, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.68/0.90            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.68/0.90       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.68/0.90            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.68/0.90  thf('4', plain,
% 0.68/0.90      (![X8 : $i, X9 : $i]:
% 0.68/0.90         ((r1_xboole_0 @ X8 @ X9)
% 0.68/0.90          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 0.68/0.90      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.68/0.90  thf('5', plain,
% 0.68/0.90      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.68/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.68/0.90  thf('6', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.90  thf('7', plain,
% 0.68/0.90      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 0.68/0.90      inference('demod', [status(thm)], ['5', '6'])).
% 0.68/0.90  thf(t28_xboole_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.68/0.90  thf('8', plain,
% 0.68/0.90      (![X12 : $i, X13 : $i]:
% 0.68/0.90         (((k3_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_tarski @ X12 @ X13))),
% 0.68/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.68/0.90  thf('9', plain,
% 0.68/0.90      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 0.68/0.90         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.68/0.90      inference('sup-', [status(thm)], ['7', '8'])).
% 0.68/0.90  thf('10', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.90  thf('11', plain,
% 0.68/0.90      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.68/0.90         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['9', '10'])).
% 0.68/0.90  thf('12', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.68/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.68/0.90  thf('13', plain,
% 0.68/0.90      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.68/0.90         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.68/0.90          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.68/0.90      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.68/0.90  thf('14', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.68/0.90          | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.68/0.90      inference('sup-', [status(thm)], ['12', '13'])).
% 0.68/0.90  thf('15', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.68/0.90          | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['11', '14'])).
% 0.68/0.90  thf(l27_zfmisc_1, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.68/0.90  thf('16', plain,
% 0.68/0.90      (![X27 : $i, X28 : $i]:
% 0.68/0.90         ((r1_xboole_0 @ (k1_tarski @ X27) @ X28) | (r2_hidden @ X27 @ X28))),
% 0.68/0.90      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.68/0.90  thf(t70_xboole_1, axiom,
% 0.68/0.90    (![A:$i,B:$i,C:$i]:
% 0.68/0.90     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.68/0.90            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.68/0.90       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.68/0.90            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.68/0.90  thf('17', plain,
% 0.68/0.90      (![X14 : $i, X15 : $i, X17 : $i]:
% 0.68/0.90         ((r1_xboole_0 @ X14 @ X15)
% 0.68/0.90          | ~ (r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X17)))),
% 0.68/0.90      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.68/0.90  thf('18', plain,
% 0.68/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.90         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.68/0.90          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 0.68/0.90      inference('sup-', [status(thm)], ['16', '17'])).
% 0.68/0.90  thf('19', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('20', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf('21', plain,
% 0.68/0.90      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.90         ((r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.68/0.90          | ~ (r1_xboole_0 @ X14 @ X15)
% 0.68/0.90          | ~ (r1_xboole_0 @ X14 @ X16))),
% 0.68/0.90      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.68/0.90  thf('22', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (r1_xboole_0 @ sk_C_2 @ X0)
% 0.68/0.90          | (r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['20', '21'])).
% 0.68/0.90  thf('23', plain, ((r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.68/0.90      inference('sup-', [status(thm)], ['19', '22'])).
% 0.68/0.90  thf('24', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 0.68/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.90  thf(t3_xboole_0, axiom,
% 0.68/0.90    (![A:$i,B:$i]:
% 0.68/0.90     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.68/0.90            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.68/0.90       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.68/0.90            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.68/0.90  thf('25', plain,
% 0.68/0.90      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.68/0.90         (~ (r2_hidden @ X6 @ X4)
% 0.68/0.90          | ~ (r2_hidden @ X6 @ X7)
% 0.68/0.90          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.68/0.90      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.68/0.90  thf('26', plain,
% 0.68/0.90      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['24', '25'])).
% 0.68/0.90  thf('27', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 0.68/0.90      inference('sup-', [status(thm)], ['23', '26'])).
% 0.68/0.90  thf('28', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 0.68/0.90      inference('sup-', [status(thm)], ['18', '27'])).
% 0.68/0.90  thf(t74_xboole_1, axiom,
% 0.68/0.90    (![A:$i,B:$i,C:$i]:
% 0.68/0.90     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.68/0.90          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.68/0.90  thf('29', plain,
% 0.68/0.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.68/0.90         (~ (r1_xboole_0 @ X18 @ X19)
% 0.68/0.90          | (r1_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20)))),
% 0.68/0.90      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.68/0.90  thf('30', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ X0))),
% 0.68/0.90      inference('sup-', [status(thm)], ['28', '29'])).
% 0.68/0.90  thf('31', plain,
% 0.68/0.90      (![X2 : $i, X3 : $i]:
% 0.68/0.90         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.68/0.90      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.68/0.90  thf('32', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ (k1_tarski @ sk_D))),
% 0.68/0.90      inference('sup-', [status(thm)], ['30', '31'])).
% 0.68/0.90  thf('33', plain,
% 0.68/0.90      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 0.68/0.90      inference('demod', [status(thm)], ['15', '32'])).
% 0.68/0.90  thf('34', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 0.68/0.90      inference('sup-', [status(thm)], ['4', '33'])).
% 0.68/0.90  thf('35', plain,
% 0.68/0.90      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.90         ((r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.68/0.90          | ~ (r1_xboole_0 @ X14 @ X15)
% 0.68/0.90          | ~ (r1_xboole_0 @ X14 @ X16))),
% 0.68/0.90      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.68/0.90  thf('36', plain,
% 0.68/0.90      (![X0 : $i]:
% 0.68/0.90         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.68/0.90          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 0.68/0.90      inference('sup-', [status(thm)], ['34', '35'])).
% 0.68/0.90  thf('37', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2))),
% 0.68/0.90      inference('sup-', [status(thm)], ['3', '36'])).
% 0.68/0.90  thf('38', plain,
% 0.68/0.90      (![X2 : $i, X3 : $i]:
% 0.68/0.90         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 0.68/0.90      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.68/0.90  thf('39', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 0.68/0.90      inference('sup-', [status(thm)], ['37', '38'])).
% 0.68/0.90  thf('40', plain, ($false), inference('demod', [status(thm)], ['0', '39'])).
% 0.68/0.90  
% 0.68/0.90  % SZS output end Refutation
% 0.68/0.90  
% 0.68/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
