%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KMMCHaah9b

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:21 EST 2020

% Result     : Theorem 7.59s
% Output     : Refutation 7.59s
% Verified   : 
% Statistics : Number of formulae       :   71 (  88 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  458 ( 685 expanded)
%              Number of equality atoms :   22 (  26 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

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
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X14 @ X13 ) @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X35 ) @ X36 )
      | ( r2_hidden @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k3_xboole_0 @ X22 @ X23 )
        = X22 )
      | ~ ( r1_tarski @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('13',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('18',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k3_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('19',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D ) ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['10','23'])).

thf('25',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    r2_hidden @ sk_D @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['24','29'])).

thf('31',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['3','30'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('36',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('37',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ X24 @ X25 )
      | ( ( k3_xboole_0 @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) )
        = ( k3_xboole_0 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_xboole_0 @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('44',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['2','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KMMCHaah9b
% 0.14/0.35  % Computer   : n005.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:02:18 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.59/7.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.59/7.77  % Solved by: fo/fo7.sh
% 7.59/7.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.59/7.77  % done 7563 iterations in 7.331s
% 7.59/7.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.59/7.77  % SZS output start Refutation
% 7.59/7.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.59/7.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.59/7.77  thf(sk_B_type, type, sk_B: $i).
% 7.59/7.77  thf(sk_C_2_type, type, sk_C_2: $i).
% 7.59/7.77  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 7.59/7.77  thf(sk_A_type, type, sk_A: $i).
% 7.59/7.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.59/7.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 7.59/7.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 7.59/7.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.59/7.77  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.59/7.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.59/7.77  thf(sk_D_type, type, sk_D: $i).
% 7.59/7.77  thf(t149_zfmisc_1, conjecture,
% 7.59/7.77    (![A:$i,B:$i,C:$i,D:$i]:
% 7.59/7.77     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 7.59/7.77         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 7.59/7.77       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 7.59/7.77  thf(zf_stmt_0, negated_conjecture,
% 7.59/7.77    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 7.59/7.77        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 7.59/7.77            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 7.59/7.77          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 7.59/7.77    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 7.59/7.77  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 7.59/7.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.77  thf(commutativity_k2_xboole_0, axiom,
% 7.59/7.77    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 7.59/7.77  thf('1', plain,
% 7.59/7.77      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 7.59/7.77      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 7.59/7.77  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 7.59/7.77      inference('demod', [status(thm)], ['0', '1'])).
% 7.59/7.77  thf(t4_xboole_0, axiom,
% 7.59/7.77    (![A:$i,B:$i]:
% 7.59/7.77     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 7.59/7.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 7.59/7.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 7.59/7.77            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 7.59/7.77  thf('3', plain,
% 7.59/7.77      (![X13 : $i, X14 : $i]:
% 7.59/7.77         ((r1_xboole_0 @ X13 @ X14)
% 7.59/7.77          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ (k3_xboole_0 @ X13 @ X14)))),
% 7.59/7.77      inference('cnf', [status(esa)], [t4_xboole_0])).
% 7.59/7.77  thf(l27_zfmisc_1, axiom,
% 7.59/7.77    (![A:$i,B:$i]:
% 7.59/7.77     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 7.59/7.77  thf('4', plain,
% 7.59/7.77      (![X35 : $i, X36 : $i]:
% 7.59/7.77         ((r1_xboole_0 @ (k1_tarski @ X35) @ X36) | (r2_hidden @ X35 @ X36))),
% 7.59/7.77      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 7.59/7.77  thf(symmetry_r1_xboole_0, axiom,
% 7.59/7.77    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 7.59/7.77  thf('5', plain,
% 7.59/7.77      (![X7 : $i, X8 : $i]:
% 7.59/7.77         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 7.59/7.77      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 7.59/7.77  thf('6', plain,
% 7.59/7.77      (![X0 : $i, X1 : $i]:
% 7.59/7.77         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 7.59/7.77      inference('sup-', [status(thm)], ['4', '5'])).
% 7.59/7.77  thf(t3_xboole_0, axiom,
% 7.59/7.77    (![A:$i,B:$i]:
% 7.59/7.77     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 7.59/7.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 7.59/7.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 7.59/7.77            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 7.59/7.77  thf('7', plain,
% 7.59/7.77      (![X9 : $i, X10 : $i]:
% 7.59/7.77         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X9))),
% 7.59/7.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 7.59/7.77  thf('8', plain,
% 7.59/7.77      (![X13 : $i, X15 : $i, X16 : $i]:
% 7.59/7.77         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 7.59/7.77          | ~ (r1_xboole_0 @ X13 @ X16))),
% 7.59/7.77      inference('cnf', [status(esa)], [t4_xboole_0])).
% 7.59/7.77  thf('9', plain,
% 7.59/7.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.59/7.77         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 7.59/7.77          | ~ (r1_xboole_0 @ X1 @ X0))),
% 7.59/7.77      inference('sup-', [status(thm)], ['7', '8'])).
% 7.59/7.77  thf('10', plain,
% 7.59/7.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.59/7.77         ((r2_hidden @ X0 @ X1)
% 7.59/7.77          | (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2))),
% 7.59/7.77      inference('sup-', [status(thm)], ['6', '9'])).
% 7.59/7.77  thf('11', plain,
% 7.59/7.77      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 7.59/7.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.77  thf(t28_xboole_1, axiom,
% 7.59/7.77    (![A:$i,B:$i]:
% 7.59/7.77     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 7.59/7.77  thf('12', plain,
% 7.59/7.77      (![X22 : $i, X23 : $i]:
% 7.59/7.77         (((k3_xboole_0 @ X22 @ X23) = (X22)) | ~ (r1_tarski @ X22 @ X23))),
% 7.59/7.77      inference('cnf', [status(esa)], [t28_xboole_1])).
% 7.59/7.77  thf('13', plain,
% 7.59/7.77      (((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))
% 7.59/7.77         = (k3_xboole_0 @ sk_A @ sk_B))),
% 7.59/7.77      inference('sup-', [status(thm)], ['11', '12'])).
% 7.59/7.77  thf(commutativity_k3_xboole_0, axiom,
% 7.59/7.77    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 7.59/7.77  thf('14', plain,
% 7.59/7.77      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 7.59/7.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.59/7.77  thf('15', plain,
% 7.59/7.77      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 7.59/7.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.59/7.77  thf('16', plain,
% 7.59/7.77      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 7.59/7.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.59/7.77  thf('17', plain,
% 7.59/7.77      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 7.59/7.77         = (k3_xboole_0 @ sk_B @ sk_A))),
% 7.59/7.77      inference('demod', [status(thm)], ['13', '14', '15', '16'])).
% 7.59/7.77  thf(t16_xboole_1, axiom,
% 7.59/7.77    (![A:$i,B:$i,C:$i]:
% 7.59/7.77     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 7.59/7.77       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 7.59/7.77  thf('18', plain,
% 7.59/7.77      (![X19 : $i, X20 : $i, X21 : $i]:
% 7.59/7.77         ((k3_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21)
% 7.59/7.77           = (k3_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21)))),
% 7.59/7.77      inference('cnf', [status(esa)], [t16_xboole_1])).
% 7.59/7.77  thf('19', plain,
% 7.59/7.77      (![X13 : $i, X15 : $i, X16 : $i]:
% 7.59/7.77         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 7.59/7.77          | ~ (r1_xboole_0 @ X13 @ X16))),
% 7.59/7.77      inference('cnf', [status(esa)], [t4_xboole_0])).
% 7.59/7.77  thf('20', plain,
% 7.59/7.77      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.59/7.77         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 7.59/7.77          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0))),
% 7.59/7.77      inference('sup-', [status(thm)], ['18', '19'])).
% 7.59/7.77  thf('21', plain,
% 7.59/7.77      (![X0 : $i]:
% 7.59/7.77         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 7.59/7.77          | ~ (r1_xboole_0 @ (k3_xboole_0 @ (k1_tarski @ sk_D) @ sk_B) @ sk_A))),
% 7.59/7.77      inference('sup-', [status(thm)], ['17', '20'])).
% 7.59/7.77  thf('22', plain,
% 7.59/7.77      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 7.59/7.77      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 7.59/7.77  thf('23', plain,
% 7.59/7.77      (![X0 : $i]:
% 7.59/7.77         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 7.59/7.77          | ~ (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D)) @ sk_A))),
% 7.59/7.77      inference('demod', [status(thm)], ['21', '22'])).
% 7.59/7.77  thf('24', plain,
% 7.59/7.77      (![X0 : $i]:
% 7.59/7.77         ((r2_hidden @ sk_D @ sk_B)
% 7.59/7.77          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 7.59/7.77      inference('sup-', [status(thm)], ['10', '23'])).
% 7.59/7.77  thf('25', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 7.59/7.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.77  thf('26', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 7.59/7.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.77  thf('27', plain,
% 7.59/7.77      (![X9 : $i, X11 : $i, X12 : $i]:
% 7.59/7.77         (~ (r2_hidden @ X11 @ X9)
% 7.59/7.77          | ~ (r2_hidden @ X11 @ X12)
% 7.59/7.77          | ~ (r1_xboole_0 @ X9 @ X12))),
% 7.59/7.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 7.59/7.77  thf('28', plain,
% 7.59/7.77      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 7.59/7.77      inference('sup-', [status(thm)], ['26', '27'])).
% 7.59/7.77  thf('29', plain, (~ (r2_hidden @ sk_D @ sk_B)),
% 7.59/7.77      inference('sup-', [status(thm)], ['25', '28'])).
% 7.59/7.77  thf('30', plain,
% 7.59/7.77      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 7.59/7.77      inference('clc', [status(thm)], ['24', '29'])).
% 7.59/7.77  thf('31', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 7.59/7.77      inference('sup-', [status(thm)], ['3', '30'])).
% 7.59/7.77  thf(d7_xboole_0, axiom,
% 7.59/7.77    (![A:$i,B:$i]:
% 7.59/7.77     ( ( r1_xboole_0 @ A @ B ) <=>
% 7.59/7.77       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 7.59/7.77  thf('32', plain,
% 7.59/7.77      (![X4 : $i, X5 : $i]:
% 7.59/7.77         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 7.59/7.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 7.59/7.77  thf('33', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 7.59/7.77      inference('sup-', [status(thm)], ['31', '32'])).
% 7.59/7.77  thf('34', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 7.59/7.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.59/7.77  thf('35', plain,
% 7.59/7.77      (![X7 : $i, X8 : $i]:
% 7.59/7.77         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 7.59/7.77      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 7.59/7.77  thf('36', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 7.59/7.77      inference('sup-', [status(thm)], ['34', '35'])).
% 7.59/7.77  thf(t78_xboole_1, axiom,
% 7.59/7.77    (![A:$i,B:$i,C:$i]:
% 7.59/7.77     ( ( r1_xboole_0 @ A @ B ) =>
% 7.59/7.77       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 7.59/7.77         ( k3_xboole_0 @ A @ C ) ) ))).
% 7.59/7.77  thf('37', plain,
% 7.59/7.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 7.59/7.77         (~ (r1_xboole_0 @ X24 @ X25)
% 7.59/7.77          | ((k3_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X26))
% 7.59/7.77              = (k3_xboole_0 @ X24 @ X26)))),
% 7.59/7.77      inference('cnf', [status(esa)], [t78_xboole_1])).
% 7.59/7.77  thf('38', plain,
% 7.59/7.77      (![X0 : $i]:
% 7.59/7.77         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ X0))
% 7.59/7.77           = (k3_xboole_0 @ sk_B @ X0))),
% 7.59/7.77      inference('sup-', [status(thm)], ['36', '37'])).
% 7.59/7.77  thf('39', plain,
% 7.59/7.77      (![X4 : $i, X6 : $i]:
% 7.59/7.77         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 7.59/7.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 7.59/7.77  thf('40', plain,
% 7.59/7.77      (![X0 : $i]:
% 7.59/7.77         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 7.59/7.77          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ X0)))),
% 7.59/7.77      inference('sup-', [status(thm)], ['38', '39'])).
% 7.59/7.77  thf('41', plain,
% 7.59/7.77      ((((k1_xboole_0) != (k1_xboole_0))
% 7.59/7.77        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ sk_A)))),
% 7.59/7.77      inference('sup-', [status(thm)], ['33', '40'])).
% 7.59/7.77  thf('42', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 7.59/7.77      inference('simplify', [status(thm)], ['41'])).
% 7.59/7.77  thf('43', plain,
% 7.59/7.77      (![X7 : $i, X8 : $i]:
% 7.59/7.77         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 7.59/7.77      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 7.59/7.77  thf('44', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 7.59/7.77      inference('sup-', [status(thm)], ['42', '43'])).
% 7.59/7.77  thf('45', plain, ($false), inference('demod', [status(thm)], ['2', '44'])).
% 7.59/7.77  
% 7.59/7.77  % SZS output end Refutation
% 7.59/7.77  
% 7.59/7.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
