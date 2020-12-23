%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fC9j5FiHSj

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:28 EST 2020

% Result     : Theorem 3.88s
% Output     : Refutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   61 (  74 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  385 ( 566 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
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
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C_1 @ X10 @ X9 ) @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ X34 )
      | ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_xboole_0 @ X17 @ X18 )
      | ( r1_xboole_0 @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_xboole_0 @ X14 @ X13 )
        = X13 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('14',plain,
    ( ( k2_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k3_xboole_0 @ X15 @ ( k2_xboole_0 @ X15 @ X16 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['21','26'])).

thf('28',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['6','27'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ X20 @ X21 )
      | ( ( k3_xboole_0 @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
        = ( k3_xboole_0 @ X20 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['5','34'])).

thf('36',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fC9j5FiHSj
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:28:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 3.88/4.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.88/4.10  % Solved by: fo/fo7.sh
% 3.88/4.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.88/4.10  % done 6966 iterations in 3.648s
% 3.88/4.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.88/4.10  % SZS output start Refutation
% 3.88/4.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.88/4.10  thf(sk_D_type, type, sk_D: $i).
% 3.88/4.10  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.88/4.10  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.88/4.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.88/4.10  thf(sk_A_type, type, sk_A: $i).
% 3.88/4.10  thf(sk_B_type, type, sk_B: $i).
% 3.88/4.10  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.88/4.10  thf(sk_C_2_type, type, sk_C_2: $i).
% 3.88/4.10  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.88/4.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.88/4.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.88/4.10  thf(t149_zfmisc_1, conjecture,
% 3.88/4.10    (![A:$i,B:$i,C:$i,D:$i]:
% 3.88/4.10     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 3.88/4.10         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 3.88/4.11       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 3.88/4.11  thf(zf_stmt_0, negated_conjecture,
% 3.88/4.11    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.88/4.11        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 3.88/4.11            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 3.88/4.11          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 3.88/4.11    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 3.88/4.11  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 3.88/4.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.11  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 3.88/4.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.11  thf(d7_xboole_0, axiom,
% 3.88/4.11    (![A:$i,B:$i]:
% 3.88/4.11     ( ( r1_xboole_0 @ A @ B ) <=>
% 3.88/4.11       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 3.88/4.11  thf('2', plain,
% 3.88/4.11      (![X2 : $i, X3 : $i]:
% 3.88/4.11         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 3.88/4.11      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.88/4.11  thf('3', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))),
% 3.88/4.11      inference('sup-', [status(thm)], ['1', '2'])).
% 3.88/4.11  thf(commutativity_k3_xboole_0, axiom,
% 3.88/4.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 3.88/4.11  thf('4', plain,
% 3.88/4.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.88/4.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.88/4.11  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 3.88/4.11      inference('demod', [status(thm)], ['3', '4'])).
% 3.88/4.11  thf(t4_xboole_0, axiom,
% 3.88/4.11    (![A:$i,B:$i]:
% 3.88/4.11     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 3.88/4.11            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.88/4.11       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.88/4.11            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 3.88/4.11  thf('6', plain,
% 3.88/4.11      (![X9 : $i, X10 : $i]:
% 3.88/4.11         ((r1_xboole_0 @ X9 @ X10)
% 3.88/4.11          | (r2_hidden @ (sk_C_1 @ X10 @ X9) @ (k3_xboole_0 @ X9 @ X10)))),
% 3.88/4.11      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.88/4.11  thf(l27_zfmisc_1, axiom,
% 3.88/4.11    (![A:$i,B:$i]:
% 3.88/4.11     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 3.88/4.11  thf('7', plain,
% 3.88/4.11      (![X33 : $i, X34 : $i]:
% 3.88/4.11         ((r1_xboole_0 @ (k1_tarski @ X33) @ X34) | (r2_hidden @ X33 @ X34))),
% 3.88/4.11      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 3.88/4.11  thf(t74_xboole_1, axiom,
% 3.88/4.11    (![A:$i,B:$i,C:$i]:
% 3.88/4.11     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 3.88/4.11          ( r1_xboole_0 @ A @ B ) ) ))).
% 3.88/4.11  thf('8', plain,
% 3.88/4.11      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.88/4.11         (~ (r1_xboole_0 @ X17 @ X18)
% 3.88/4.11          | (r1_xboole_0 @ X17 @ (k3_xboole_0 @ X18 @ X19)))),
% 3.88/4.11      inference('cnf', [status(esa)], [t74_xboole_1])).
% 3.88/4.11  thf('9', plain,
% 3.88/4.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.11         ((r2_hidden @ X1 @ X0)
% 3.88/4.11          | (r1_xboole_0 @ (k1_tarski @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 3.88/4.11      inference('sup-', [status(thm)], ['7', '8'])).
% 3.88/4.11  thf('10', plain,
% 3.88/4.11      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 3.88/4.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.11  thf('11', plain,
% 3.88/4.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.88/4.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.88/4.11  thf('12', plain,
% 3.88/4.11      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 3.88/4.11      inference('demod', [status(thm)], ['10', '11'])).
% 3.88/4.11  thf(t12_xboole_1, axiom,
% 3.88/4.11    (![A:$i,B:$i]:
% 3.88/4.11     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.88/4.11  thf('13', plain,
% 3.88/4.11      (![X13 : $i, X14 : $i]:
% 3.88/4.11         (((k2_xboole_0 @ X14 @ X13) = (X13)) | ~ (r1_tarski @ X14 @ X13))),
% 3.88/4.11      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.88/4.11  thf('14', plain,
% 3.88/4.11      (((k2_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 3.88/4.11         = (k1_tarski @ sk_D))),
% 3.88/4.11      inference('sup-', [status(thm)], ['12', '13'])).
% 3.88/4.11  thf(t21_xboole_1, axiom,
% 3.88/4.11    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 3.88/4.11  thf('15', plain,
% 3.88/4.11      (![X15 : $i, X16 : $i]:
% 3.88/4.11         ((k3_xboole_0 @ X15 @ (k2_xboole_0 @ X15 @ X16)) = (X15))),
% 3.88/4.11      inference('cnf', [status(esa)], [t21_xboole_1])).
% 3.88/4.11  thf('16', plain,
% 3.88/4.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.88/4.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.88/4.11  thf('17', plain,
% 3.88/4.11      (![X9 : $i, X11 : $i, X12 : $i]:
% 3.88/4.11         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 3.88/4.11          | ~ (r1_xboole_0 @ X9 @ X12))),
% 3.88/4.11      inference('cnf', [status(esa)], [t4_xboole_0])).
% 3.88/4.11  thf('18', plain,
% 3.88/4.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.11         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 3.88/4.11          | ~ (r1_xboole_0 @ X0 @ X1))),
% 3.88/4.11      inference('sup-', [status(thm)], ['16', '17'])).
% 3.88/4.11  thf('19', plain,
% 3.88/4.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.88/4.11         (~ (r2_hidden @ X2 @ X0)
% 3.88/4.11          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0))),
% 3.88/4.11      inference('sup-', [status(thm)], ['15', '18'])).
% 3.88/4.11  thf('20', plain,
% 3.88/4.11      (![X0 : $i]:
% 3.88/4.11         (~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 3.88/4.11          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 3.88/4.11      inference('sup-', [status(thm)], ['14', '19'])).
% 3.88/4.11  thf('21', plain,
% 3.88/4.11      (![X0 : $i]:
% 3.88/4.11         ((r2_hidden @ sk_D @ sk_B)
% 3.88/4.11          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 3.88/4.11      inference('sup-', [status(thm)], ['9', '20'])).
% 3.88/4.11  thf('22', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 3.88/4.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.11  thf('23', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 3.88/4.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.88/4.11  thf(t3_xboole_0, axiom,
% 3.88/4.11    (![A:$i,B:$i]:
% 3.88/4.11     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.88/4.11            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.88/4.11       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.88/4.11            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.88/4.11  thf('24', plain,
% 3.88/4.11      (![X5 : $i, X7 : $i, X8 : $i]:
% 3.88/4.11         (~ (r2_hidden @ X7 @ X5)
% 3.88/4.11          | ~ (r2_hidden @ X7 @ X8)
% 3.88/4.11          | ~ (r1_xboole_0 @ X5 @ X8))),
% 3.88/4.11      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.88/4.11  thf('25', plain,
% 3.88/4.11      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 3.88/4.11      inference('sup-', [status(thm)], ['23', '24'])).
% 3.88/4.11  thf('26', plain, (~ (r2_hidden @ sk_D @ sk_B)),
% 3.88/4.11      inference('sup-', [status(thm)], ['22', '25'])).
% 3.88/4.11  thf('27', plain,
% 3.88/4.11      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 3.88/4.11      inference('clc', [status(thm)], ['21', '26'])).
% 3.88/4.11  thf('28', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 3.88/4.11      inference('sup-', [status(thm)], ['6', '27'])).
% 3.88/4.11  thf(t78_xboole_1, axiom,
% 3.88/4.11    (![A:$i,B:$i,C:$i]:
% 3.88/4.11     ( ( r1_xboole_0 @ A @ B ) =>
% 3.88/4.11       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 3.88/4.11         ( k3_xboole_0 @ A @ C ) ) ))).
% 3.88/4.11  thf('29', plain,
% 3.88/4.11      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.88/4.11         (~ (r1_xboole_0 @ X20 @ X21)
% 3.88/4.11          | ((k3_xboole_0 @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 3.88/4.11              = (k3_xboole_0 @ X20 @ X22)))),
% 3.88/4.11      inference('cnf', [status(esa)], [t78_xboole_1])).
% 3.88/4.11  thf('30', plain,
% 3.88/4.11      (![X0 : $i]:
% 3.88/4.11         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0))
% 3.88/4.11           = (k3_xboole_0 @ sk_B @ X0))),
% 3.88/4.11      inference('sup-', [status(thm)], ['28', '29'])).
% 3.88/4.11  thf('31', plain,
% 3.88/4.11      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 3.88/4.11      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 3.88/4.11  thf('32', plain,
% 3.88/4.11      (![X2 : $i, X4 : $i]:
% 3.88/4.11         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 3.88/4.11      inference('cnf', [status(esa)], [d7_xboole_0])).
% 3.88/4.11  thf('33', plain,
% 3.88/4.11      (![X0 : $i, X1 : $i]:
% 3.88/4.11         (((k3_xboole_0 @ X1 @ X0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ X1))),
% 3.88/4.11      inference('sup-', [status(thm)], ['31', '32'])).
% 3.88/4.11  thf('34', plain,
% 3.88/4.11      (![X0 : $i]:
% 3.88/4.11         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 3.88/4.11          | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ X0) @ sk_B))),
% 3.88/4.11      inference('sup-', [status(thm)], ['30', '33'])).
% 3.88/4.11  thf('35', plain,
% 3.88/4.11      ((((k1_xboole_0) != (k1_xboole_0))
% 3.88/4.11        | (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B))),
% 3.88/4.11      inference('sup-', [status(thm)], ['5', '34'])).
% 3.88/4.11  thf('36', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 3.88/4.11      inference('simplify', [status(thm)], ['35'])).
% 3.88/4.11  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 3.88/4.11  
% 3.88/4.11  % SZS output end Refutation
% 3.88/4.11  
% 3.88/4.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
