%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a2b0u0YnU0

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:29 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   76 (  92 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   16
%              Number of atoms          :  481 ( 680 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('7',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(simplify,[status(thm)],['7'])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k4_xboole_0 @ X38 @ ( k1_tarski @ X39 ) )
        = X38 )
      | ( r2_hidden @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

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

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ X28 @ X29 )
      | ( r1_xboole_0 @ X28 @ ( k4_xboole_0 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ sk_D ) ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_A @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('21',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X23 @ X24 ) @ X24 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('24',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['20','25'])).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k3_xboole_0 @ X13 @ ( k3_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
      = ( k3_xboole_0 @ sk_A @ k1_xboole_0 ) )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['19','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('31',plain,(
    ! [X18: $i] :
      ( r1_xboole_0 @ X18 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k3_xboole_0 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','33'])).

thf('35',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r2_hidden @ sk_D @ sk_C_1 ),
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

thf('37',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X7 )
      | ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X7 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference(simplify,[status(thm)],['42'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_xboole_0 @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','45'])).

thf('47',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a2b0u0YnU0
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.37/1.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.37/1.59  % Solved by: fo/fo7.sh
% 1.37/1.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.37/1.59  % done 3311 iterations in 1.138s
% 1.37/1.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.37/1.59  % SZS output start Refutation
% 1.37/1.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.37/1.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.37/1.59  thf(sk_A_type, type, sk_A: $i).
% 1.37/1.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.37/1.59  thf(sk_D_type, type, sk_D: $i).
% 1.37/1.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.37/1.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.37/1.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.37/1.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.37/1.59  thf(sk_B_type, type, sk_B: $i).
% 1.37/1.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.37/1.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.37/1.59  thf(t149_zfmisc_1, conjecture,
% 1.37/1.59    (![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.59     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.37/1.59         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.37/1.59       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.37/1.59  thf(zf_stmt_0, negated_conjecture,
% 1.37/1.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.37/1.59        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.37/1.59            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.37/1.59          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.37/1.59    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.37/1.59  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.37/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.59  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.37/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.59  thf(d7_xboole_0, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.37/1.59       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.37/1.59  thf('2', plain,
% 1.37/1.59      (![X2 : $i, X3 : $i]:
% 1.37/1.59         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.37/1.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.37/1.59  thf('3', plain, (((k3_xboole_0 @ sk_C_1 @ sk_B) = (k1_xboole_0))),
% 1.37/1.59      inference('sup-', [status(thm)], ['1', '2'])).
% 1.37/1.59  thf(commutativity_k3_xboole_0, axiom,
% 1.37/1.59    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.37/1.59  thf('4', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.37/1.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.37/1.59  thf('5', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 1.37/1.59      inference('demod', [status(thm)], ['3', '4'])).
% 1.37/1.59  thf('6', plain,
% 1.37/1.59      (![X2 : $i, X4 : $i]:
% 1.37/1.59         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.37/1.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.37/1.59  thf('7', plain,
% 1.37/1.59      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_1))),
% 1.37/1.59      inference('sup-', [status(thm)], ['5', '6'])).
% 1.37/1.59  thf('8', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 1.37/1.59      inference('simplify', [status(thm)], ['7'])).
% 1.37/1.59  thf(t65_zfmisc_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 1.37/1.59       ( ~( r2_hidden @ B @ A ) ) ))).
% 1.37/1.59  thf('9', plain,
% 1.37/1.59      (![X38 : $i, X39 : $i]:
% 1.37/1.59         (((k4_xboole_0 @ X38 @ (k1_tarski @ X39)) = (X38))
% 1.37/1.59          | (r2_hidden @ X39 @ X38))),
% 1.37/1.59      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 1.37/1.59  thf('10', plain,
% 1.37/1.59      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.37/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.59  thf('11', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.37/1.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.37/1.59  thf('12', plain,
% 1.37/1.59      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.37/1.59      inference('demod', [status(thm)], ['10', '11'])).
% 1.37/1.59  thf(t85_xboole_1, axiom,
% 1.37/1.59    (![A:$i,B:$i,C:$i]:
% 1.37/1.59     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 1.37/1.59  thf('13', plain,
% 1.37/1.59      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.37/1.59         (~ (r1_tarski @ X28 @ X29)
% 1.37/1.59          | (r1_xboole_0 @ X28 @ (k4_xboole_0 @ X30 @ X29)))),
% 1.37/1.59      inference('cnf', [status(esa)], [t85_xboole_1])).
% 1.37/1.59  thf('14', plain,
% 1.37/1.59      (![X0 : $i]:
% 1.37/1.59         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 1.37/1.59          (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['12', '13'])).
% 1.37/1.59  thf('15', plain,
% 1.37/1.59      (![X2 : $i, X3 : $i]:
% 1.37/1.59         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.37/1.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.37/1.59  thf('16', plain,
% 1.37/1.59      (![X0 : $i]:
% 1.37/1.59         ((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ 
% 1.37/1.59           (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D))) = (k1_xboole_0))),
% 1.37/1.59      inference('sup-', [status(thm)], ['14', '15'])).
% 1.37/1.59  thf(t16_xboole_1, axiom,
% 1.37/1.59    (![A:$i,B:$i,C:$i]:
% 1.37/1.59     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 1.37/1.59       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.37/1.59  thf('17', plain,
% 1.37/1.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.37/1.59         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 1.37/1.59           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.37/1.59      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.37/1.59  thf('18', plain,
% 1.37/1.59      (![X0 : $i]:
% 1.37/1.59         ((k3_xboole_0 @ sk_B @ 
% 1.37/1.59           (k3_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ (k1_tarski @ sk_D))))
% 1.37/1.59           = (k1_xboole_0))),
% 1.37/1.59      inference('demod', [status(thm)], ['16', '17'])).
% 1.37/1.59  thf('19', plain,
% 1.37/1.59      (![X0 : $i]:
% 1.37/1.59         (((k3_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_A @ X0)) = (k1_xboole_0))
% 1.37/1.59          | (r2_hidden @ sk_D @ X0))),
% 1.37/1.59      inference('sup+', [status(thm)], ['9', '18'])).
% 1.37/1.59  thf(t48_xboole_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.37/1.59  thf('20', plain,
% 1.37/1.59      (![X16 : $i, X17 : $i]:
% 1.37/1.59         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 1.37/1.59           = (k3_xboole_0 @ X16 @ X17))),
% 1.37/1.59      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.37/1.59  thf(t79_xboole_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 1.37/1.59  thf('21', plain,
% 1.37/1.59      (![X23 : $i, X24 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X23 @ X24) @ X24)),
% 1.37/1.59      inference('cnf', [status(esa)], [t79_xboole_1])).
% 1.37/1.59  thf(symmetry_r1_xboole_0, axiom,
% 1.37/1.59    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.37/1.59  thf('22', plain,
% 1.37/1.59      (![X5 : $i, X6 : $i]:
% 1.37/1.59         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.37/1.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.37/1.59  thf('23', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 1.37/1.59      inference('sup-', [status(thm)], ['21', '22'])).
% 1.37/1.59  thf(t83_xboole_1, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.37/1.59  thf('24', plain,
% 1.37/1.59      (![X25 : $i, X26 : $i]:
% 1.37/1.59         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 1.37/1.59      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.37/1.59  thf('25', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 1.37/1.59      inference('sup-', [status(thm)], ['23', '24'])).
% 1.37/1.59  thf('26', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 1.37/1.59      inference('sup+', [status(thm)], ['20', '25'])).
% 1.37/1.59  thf('27', plain,
% 1.37/1.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.37/1.59         ((k3_xboole_0 @ (k3_xboole_0 @ X13 @ X14) @ X15)
% 1.37/1.59           = (k3_xboole_0 @ X13 @ (k3_xboole_0 @ X14 @ X15)))),
% 1.37/1.59      inference('cnf', [status(esa)], [t16_xboole_1])).
% 1.37/1.59  thf('28', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]:
% 1.37/1.59         ((k3_xboole_0 @ X1 @ X0)
% 1.37/1.59           = (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.37/1.59      inference('sup+', [status(thm)], ['26', '27'])).
% 1.37/1.59  thf('29', plain,
% 1.37/1.59      ((((k3_xboole_0 @ sk_A @ sk_B) = (k3_xboole_0 @ sk_A @ k1_xboole_0))
% 1.37/1.59        | (r2_hidden @ sk_D @ sk_B))),
% 1.37/1.59      inference('sup+', [status(thm)], ['19', '28'])).
% 1.37/1.59  thf('30', plain,
% 1.37/1.59      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.37/1.59      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.37/1.59  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.37/1.59  thf('31', plain, (![X18 : $i]: (r1_xboole_0 @ X18 @ k1_xboole_0)),
% 1.37/1.59      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.37/1.59  thf('32', plain,
% 1.37/1.59      (![X2 : $i, X3 : $i]:
% 1.37/1.59         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 1.37/1.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.37/1.59  thf('33', plain,
% 1.37/1.59      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.37/1.59      inference('sup-', [status(thm)], ['31', '32'])).
% 1.37/1.59  thf('34', plain,
% 1.37/1.59      ((((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))
% 1.37/1.59        | (r2_hidden @ sk_D @ sk_B))),
% 1.37/1.59      inference('demod', [status(thm)], ['29', '30', '33'])).
% 1.37/1.59  thf('35', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 1.37/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.59  thf('36', plain, ((r2_hidden @ sk_D @ sk_C_1)),
% 1.37/1.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.37/1.59  thf(t3_xboole_0, axiom,
% 1.37/1.59    (![A:$i,B:$i]:
% 1.37/1.59     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.37/1.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.37/1.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.37/1.59            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.37/1.59  thf('37', plain,
% 1.37/1.59      (![X7 : $i, X9 : $i, X10 : $i]:
% 1.37/1.59         (~ (r2_hidden @ X9 @ X7)
% 1.37/1.59          | ~ (r2_hidden @ X9 @ X10)
% 1.37/1.59          | ~ (r1_xboole_0 @ X7 @ X10))),
% 1.37/1.59      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.37/1.59  thf('38', plain,
% 1.37/1.59      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_1 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.37/1.59      inference('sup-', [status(thm)], ['36', '37'])).
% 1.37/1.59  thf('39', plain, (~ (r2_hidden @ sk_D @ sk_B)),
% 1.37/1.59      inference('sup-', [status(thm)], ['35', '38'])).
% 1.37/1.59  thf('40', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.37/1.59      inference('clc', [status(thm)], ['34', '39'])).
% 1.37/1.59  thf('41', plain,
% 1.37/1.59      (![X2 : $i, X4 : $i]:
% 1.37/1.59         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 1.37/1.59      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.37/1.59  thf('42', plain,
% 1.37/1.59      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_A))),
% 1.37/1.59      inference('sup-', [status(thm)], ['40', '41'])).
% 1.37/1.59  thf('43', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.37/1.59      inference('simplify', [status(thm)], ['42'])).
% 1.37/1.59  thf(t70_xboole_1, axiom,
% 1.37/1.59    (![A:$i,B:$i,C:$i]:
% 1.37/1.59     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 1.37/1.59            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 1.37/1.59       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 1.37/1.59            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 1.37/1.59  thf('44', plain,
% 1.37/1.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.37/1.59         ((r1_xboole_0 @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 1.37/1.59          | ~ (r1_xboole_0 @ X19 @ X20)
% 1.37/1.59          | ~ (r1_xboole_0 @ X19 @ X21))),
% 1.37/1.59      inference('cnf', [status(esa)], [t70_xboole_1])).
% 1.37/1.59  thf('45', plain,
% 1.37/1.59      (![X0 : $i]:
% 1.37/1.59         (~ (r1_xboole_0 @ sk_B @ X0)
% 1.37/1.59          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 1.37/1.59      inference('sup-', [status(thm)], ['43', '44'])).
% 1.37/1.59  thf('46', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 1.37/1.59      inference('sup-', [status(thm)], ['8', '45'])).
% 1.37/1.59  thf('47', plain,
% 1.37/1.59      (![X5 : $i, X6 : $i]:
% 1.37/1.59         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 1.37/1.59      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.37/1.59  thf('48', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 1.37/1.59      inference('sup-', [status(thm)], ['46', '47'])).
% 1.37/1.59  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 1.37/1.59  
% 1.37/1.59  % SZS output end Refutation
% 1.37/1.59  
% 1.37/1.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
