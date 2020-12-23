%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xkzAo1O6Vs

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:30 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   65 (  81 expanded)
%              Number of leaves         :   22 (  33 expanded)
%              Depth                    :   15
%              Number of atoms          :  415 ( 675 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X33 ) @ X34 )
      | ( r2_hidden @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ( r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_C_2 @ ( k2_xboole_0 @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
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

thf('13',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( r2_hidden @ sk_D @ ( k2_xboole_0 @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('18',plain,(
    r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) )
    = sk_B ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ X24 @ X25 )
      | ( r1_xboole_0 @ X24 @ ( k4_xboole_0 @ X26 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_B ),
    inference('sup+',[status(thm)],['20','25'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ X18 @ X19 )
      | ( r1_xboole_0 @ X18 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ( r2_hidden @ ( sk_C_1 @ X9 @ X8 ) @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('31',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r1_xboole_0 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
      | ~ ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['3','37'])).

thf('39',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('40',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference(demod,[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xkzAo1O6Vs
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.38/1.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.38/1.57  % Solved by: fo/fo7.sh
% 1.38/1.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.38/1.57  % done 2603 iterations in 1.123s
% 1.38/1.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.38/1.57  % SZS output start Refutation
% 1.38/1.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.38/1.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.38/1.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.38/1.57  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.38/1.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.38/1.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.38/1.57  thf(sk_A_type, type, sk_A: $i).
% 1.38/1.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.38/1.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.38/1.57  thf(sk_B_type, type, sk_B: $i).
% 1.38/1.57  thf(sk_D_type, type, sk_D: $i).
% 1.38/1.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.38/1.57  thf(t149_zfmisc_1, conjecture,
% 1.38/1.57    (![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.57     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.38/1.57         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.38/1.57       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.38/1.57  thf(zf_stmt_0, negated_conjecture,
% 1.38/1.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.38/1.57        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.38/1.57            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.38/1.57          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.38/1.57    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.38/1.57  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf('1', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf(symmetry_r1_xboole_0, axiom,
% 1.38/1.57    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.38/1.57  thf('2', plain,
% 1.38/1.57      (![X2 : $i, X3 : $i]:
% 1.38/1.57         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.38/1.57      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.38/1.57  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 1.38/1.57      inference('sup-', [status(thm)], ['1', '2'])).
% 1.38/1.57  thf(l27_zfmisc_1, axiom,
% 1.38/1.57    (![A:$i,B:$i]:
% 1.38/1.57     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 1.38/1.57  thf('4', plain,
% 1.38/1.57      (![X33 : $i, X34 : $i]:
% 1.38/1.57         ((r1_xboole_0 @ (k1_tarski @ X33) @ X34) | (r2_hidden @ X33 @ X34))),
% 1.38/1.57      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 1.38/1.57  thf(t70_xboole_1, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i]:
% 1.38/1.57     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.38/1.57            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.38/1.57       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.38/1.57            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.38/1.57  thf('5', plain,
% 1.38/1.57      (![X14 : $i, X15 : $i, X17 : $i]:
% 1.38/1.57         ((r1_xboole_0 @ X14 @ X15)
% 1.38/1.57          | ~ (r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X17)))),
% 1.38/1.57      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.38/1.57  thf('6', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.57         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 1.38/1.57          | (r1_xboole_0 @ (k1_tarski @ X2) @ X1))),
% 1.38/1.57      inference('sup-', [status(thm)], ['4', '5'])).
% 1.38/1.57  thf('7', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf('8', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf('9', plain,
% 1.38/1.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.38/1.57         ((r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 1.38/1.57          | ~ (r1_xboole_0 @ X14 @ X15)
% 1.38/1.57          | ~ (r1_xboole_0 @ X14 @ X16))),
% 1.38/1.57      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.38/1.57  thf('10', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (~ (r1_xboole_0 @ sk_C_2 @ X0)
% 1.38/1.57          | (r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ X0)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['8', '9'])).
% 1.38/1.57  thf('11', plain, ((r1_xboole_0 @ sk_C_2 @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.38/1.57      inference('sup-', [status(thm)], ['7', '10'])).
% 1.38/1.57  thf('12', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf(t3_xboole_0, axiom,
% 1.38/1.57    (![A:$i,B:$i]:
% 1.38/1.57     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.38/1.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.38/1.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.38/1.57            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.38/1.57  thf('13', plain,
% 1.38/1.57      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.38/1.57         (~ (r2_hidden @ X6 @ X4)
% 1.38/1.57          | ~ (r2_hidden @ X6 @ X7)
% 1.38/1.57          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.38/1.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.57  thf('14', plain,
% 1.38/1.57      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.38/1.57      inference('sup-', [status(thm)], ['12', '13'])).
% 1.38/1.57  thf('15', plain, (~ (r2_hidden @ sk_D @ (k2_xboole_0 @ sk_B @ sk_B))),
% 1.38/1.57      inference('sup-', [status(thm)], ['11', '14'])).
% 1.38/1.57  thf('16', plain, ((r1_xboole_0 @ (k1_tarski @ sk_D) @ sk_B)),
% 1.38/1.57      inference('sup-', [status(thm)], ['6', '15'])).
% 1.38/1.57  thf('17', plain,
% 1.38/1.57      (![X2 : $i, X3 : $i]:
% 1.38/1.57         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.38/1.57      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.38/1.57  thf('18', plain, ((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_D))),
% 1.38/1.57      inference('sup-', [status(thm)], ['16', '17'])).
% 1.38/1.57  thf(t83_xboole_1, axiom,
% 1.38/1.57    (![A:$i,B:$i]:
% 1.38/1.57     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.38/1.57  thf('19', plain,
% 1.38/1.57      (![X21 : $i, X22 : $i]:
% 1.38/1.57         (((k4_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_xboole_0 @ X21 @ X22))),
% 1.38/1.57      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.38/1.57  thf('20', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) = (sk_B))),
% 1.38/1.57      inference('sup-', [status(thm)], ['18', '19'])).
% 1.38/1.57  thf('21', plain,
% 1.38/1.57      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.38/1.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.38/1.57  thf(commutativity_k3_xboole_0, axiom,
% 1.38/1.57    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.38/1.57  thf('22', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.38/1.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.38/1.57  thf('23', plain,
% 1.38/1.57      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.38/1.57      inference('demod', [status(thm)], ['21', '22'])).
% 1.38/1.57  thf(t85_xboole_1, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i]:
% 1.38/1.57     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.38/1.57  thf('24', plain,
% 1.38/1.57      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.38/1.57         (~ (r1_tarski @ X24 @ X25)
% 1.38/1.57          | (r1_xboole_0 @ X24 @ (k4_xboole_0 @ X26 @ X25)))),
% 1.38/1.57      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.38/1.57  thf('25', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 1.38/1.57          (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['23', '24'])).
% 1.38/1.57  thf('26', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_B)),
% 1.38/1.57      inference('sup+', [status(thm)], ['20', '25'])).
% 1.38/1.57  thf(t74_xboole_1, axiom,
% 1.38/1.57    (![A:$i,B:$i,C:$i]:
% 1.38/1.57     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 1.38/1.57          ( r1_xboole_0 @ A @ B ) ) ))).
% 1.38/1.57  thf('27', plain,
% 1.38/1.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.38/1.57         (~ (r1_xboole_0 @ X18 @ X19)
% 1.38/1.57          | (r1_xboole_0 @ X18 @ (k3_xboole_0 @ X19 @ X20)))),
% 1.38/1.57      inference('cnf', [status(esa)], [t74_xboole_1])).
% 1.38/1.57  thf('28', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k3_xboole_0 @ sk_B @ X0))),
% 1.38/1.57      inference('sup-', [status(thm)], ['26', '27'])).
% 1.38/1.57  thf(t4_xboole_0, axiom,
% 1.38/1.57    (![A:$i,B:$i]:
% 1.38/1.57     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.38/1.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.38/1.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.38/1.57            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.38/1.57  thf('29', plain,
% 1.38/1.57      (![X8 : $i, X9 : $i]:
% 1.38/1.57         ((r1_xboole_0 @ X8 @ X9)
% 1.38/1.57          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.38/1.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.38/1.57  thf('30', plain,
% 1.38/1.57      (![X8 : $i, X9 : $i]:
% 1.38/1.57         ((r1_xboole_0 @ X8 @ X9)
% 1.38/1.57          | (r2_hidden @ (sk_C_1 @ X9 @ X8) @ (k3_xboole_0 @ X8 @ X9)))),
% 1.38/1.57      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.38/1.57  thf('31', plain,
% 1.38/1.57      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.38/1.57         (~ (r2_hidden @ X6 @ X4)
% 1.38/1.57          | ~ (r2_hidden @ X6 @ X7)
% 1.38/1.57          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.38/1.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.38/1.57  thf('32', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.38/1.57         ((r1_xboole_0 @ X1 @ X0)
% 1.38/1.57          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 1.38/1.57          | ~ (r2_hidden @ (sk_C_1 @ X0 @ X1) @ X2))),
% 1.38/1.57      inference('sup-', [status(thm)], ['30', '31'])).
% 1.38/1.57  thf('33', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         ((r1_xboole_0 @ X1 @ X0)
% 1.38/1.57          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.38/1.57          | (r1_xboole_0 @ X1 @ X0))),
% 1.38/1.57      inference('sup-', [status(thm)], ['29', '32'])).
% 1.38/1.57  thf('34', plain,
% 1.38/1.57      (![X0 : $i, X1 : $i]:
% 1.38/1.57         (~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 1.38/1.57          | (r1_xboole_0 @ X1 @ X0))),
% 1.38/1.57      inference('simplify', [status(thm)], ['33'])).
% 1.38/1.57  thf('35', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.38/1.57      inference('sup-', [status(thm)], ['28', '34'])).
% 1.38/1.57  thf('36', plain,
% 1.38/1.57      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.38/1.57         ((r1_xboole_0 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 1.38/1.57          | ~ (r1_xboole_0 @ X14 @ X15)
% 1.38/1.57          | ~ (r1_xboole_0 @ X14 @ X16))),
% 1.38/1.57      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.38/1.57  thf('37', plain,
% 1.38/1.57      (![X0 : $i]:
% 1.38/1.57         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.38/1.57          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.38/1.57      inference('sup-', [status(thm)], ['35', '36'])).
% 1.38/1.57  thf('38', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_2))),
% 1.38/1.57      inference('sup-', [status(thm)], ['3', '37'])).
% 1.38/1.57  thf('39', plain,
% 1.38/1.57      (![X2 : $i, X3 : $i]:
% 1.38/1.57         ((r1_xboole_0 @ X2 @ X3) | ~ (r1_xboole_0 @ X3 @ X2))),
% 1.38/1.57      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.38/1.57  thf('40', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.38/1.57      inference('sup-', [status(thm)], ['38', '39'])).
% 1.38/1.57  thf('41', plain, ($false), inference('demod', [status(thm)], ['0', '40'])).
% 1.38/1.57  
% 1.38/1.57  % SZS output end Refutation
% 1.38/1.57  
% 1.38/1.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
