%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qE3NB8pzp7

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:26:43 EST 2020

% Result     : Theorem 4.47s
% Output     : Refutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 187 expanded)
%              Number of leaves         :   22 (  57 expanded)
%              Depth                    :   14
%              Number of atoms          :  589 (2010 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t107_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) )
      <=> ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t107_xboole_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t93_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_xboole_0 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k5_xboole_0 @ X32 @ X33 ) @ ( k3_xboole_0 @ X32 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t93_xboole_1])).

thf('3',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('6',plain,
    ( ( ( k3_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      = sk_A )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('8',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_A @ X0 ) ) @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('10',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ ( k2_xboole_0 @ ( k5_xboole_0 @ sk_B @ sk_C ) @ X0 ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(l97_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l97_xboole_1])).

thf('15',plain,
    ( ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('17',plain,
    ( ( ( k2_xboole_0 @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
      = ( k5_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('18',plain,(
    ! [X26: $i,X27: $i,X29: $i] :
      ( ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( r1_xboole_0 @ X26 @ ( k2_xboole_0 @ X27 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('19',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ X0 @ ( k5_xboole_0 @ sk_B @ sk_C ) )
        | ( r1_xboole_0 @ X0 @ sk_A ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','19'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('22',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ~ ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,(
    ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sat_resolution*',[status(thm)],['13','24','25'])).

thf('27',plain,(
    ~ ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['28'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('30',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X30 @ X31 ) @ X31 )
        = X30 )
      | ~ ( r1_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X18 @ X19 ) @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('32',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k4_xboole_0 @ X30 @ X31 )
        = X30 )
      | ~ ( r1_xboole_0 @ X30 @ X31 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
      = sk_A )
   <= ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['28'])).

thf('35',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['13','24','25','34'])).

thf('36',plain,
    ( ( k4_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    = sk_A ),
    inference(simpl_trail,[status(thm)],['33','35'])).

thf('37',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
   <= ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('38',plain,
    ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) )
    | ( r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(split,[status(esa)],['3'])).

thf('39',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['13','24','25','38'])).

thf('40',plain,(
    r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['37','39'])).

thf(t33_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ ( k4_xboole_0 @ X15 @ X17 ) @ ( k4_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t33_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ sk_A @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['36','42'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k5_xboole_0 @ X4 @ X5 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf('45',plain,(
    r1_tarski @ sk_A @ ( k5_xboole_0 @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['27','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qE3NB8pzp7
% 0.11/0.32  % Computer   : n013.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 09:41:09 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 4.47/4.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.47/4.72  % Solved by: fo/fo7.sh
% 4.47/4.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.47/4.72  % done 2738 iterations in 4.269s
% 4.47/4.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.47/4.72  % SZS output start Refutation
% 4.47/4.72  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 4.47/4.72  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.47/4.72  thf(sk_B_type, type, sk_B: $i).
% 4.47/4.72  thf(sk_A_type, type, sk_A: $i).
% 4.47/4.72  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 4.47/4.72  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.47/4.72  thf(sk_C_type, type, sk_C: $i).
% 4.47/4.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.47/4.72  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 4.47/4.72  thf(t107_xboole_1, conjecture,
% 4.47/4.72    (![A:$i,B:$i,C:$i]:
% 4.47/4.72     ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 4.47/4.72       ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 4.47/4.72         ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 4.47/4.72  thf(zf_stmt_0, negated_conjecture,
% 4.47/4.72    (~( ![A:$i,B:$i,C:$i]:
% 4.47/4.72        ( ( r1_tarski @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 4.47/4.72          ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & 
% 4.47/4.72            ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 4.47/4.72    inference('cnf.neg', [status(esa)], [t107_xboole_1])).
% 4.47/4.72  thf('0', plain,
% 4.47/4.72      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 4.47/4.72        | ~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 4.47/4.72        | ~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.72  thf('1', plain,
% 4.47/4.72      ((~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 4.47/4.72         <= (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('split', [status(esa)], ['0'])).
% 4.47/4.72  thf(t93_xboole_1, axiom,
% 4.47/4.72    (![A:$i,B:$i]:
% 4.47/4.72     ( ( k2_xboole_0 @ A @ B ) =
% 4.47/4.72       ( k2_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.47/4.72  thf('2', plain,
% 4.47/4.72      (![X32 : $i, X33 : $i]:
% 4.47/4.72         ((k2_xboole_0 @ X32 @ X33)
% 4.47/4.72           = (k2_xboole_0 @ (k5_xboole_0 @ X32 @ X33) @ 
% 4.47/4.72              (k3_xboole_0 @ X32 @ X33)))),
% 4.47/4.72      inference('cnf', [status(esa)], [t93_xboole_1])).
% 4.47/4.72  thf('3', plain,
% 4.47/4.72      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))
% 4.47/4.72        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.72  thf('4', plain,
% 4.47/4.72      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 4.47/4.72         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('split', [status(esa)], ['3'])).
% 4.47/4.72  thf(t28_xboole_1, axiom,
% 4.47/4.72    (![A:$i,B:$i]:
% 4.47/4.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 4.47/4.72  thf('5', plain,
% 4.47/4.72      (![X10 : $i, X11 : $i]:
% 4.47/4.72         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 4.47/4.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 4.47/4.72  thf('6', plain,
% 4.47/4.72      ((((k3_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)) = (sk_A)))
% 4.47/4.72         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('sup-', [status(thm)], ['4', '5'])).
% 4.47/4.72  thf(t31_xboole_1, axiom,
% 4.47/4.72    (![A:$i,B:$i,C:$i]:
% 4.47/4.72     ( r1_tarski @
% 4.47/4.72       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 4.47/4.72       ( k2_xboole_0 @ B @ C ) ))).
% 4.47/4.72  thf('7', plain,
% 4.47/4.72      (![X12 : $i, X13 : $i, X14 : $i]:
% 4.47/4.72         (r1_tarski @ 
% 4.47/4.72          (k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k3_xboole_0 @ X12 @ X14)) @ 
% 4.47/4.72          (k2_xboole_0 @ X13 @ X14))),
% 4.47/4.72      inference('cnf', [status(esa)], [t31_xboole_1])).
% 4.47/4.72  thf('8', plain,
% 4.47/4.72      ((![X0 : $i]:
% 4.47/4.72          (r1_tarski @ (k2_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_A @ X0)) @ 
% 4.47/4.72           (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0)))
% 4.47/4.72         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('sup+', [status(thm)], ['6', '7'])).
% 4.47/4.72  thf(t22_xboole_1, axiom,
% 4.47/4.72    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 4.47/4.72  thf('9', plain,
% 4.47/4.72      (![X8 : $i, X9 : $i]:
% 4.47/4.72         ((k2_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)) = (X8))),
% 4.47/4.72      inference('cnf', [status(esa)], [t22_xboole_1])).
% 4.47/4.72  thf('10', plain,
% 4.47/4.72      ((![X0 : $i]:
% 4.47/4.72          (r1_tarski @ sk_A @ (k2_xboole_0 @ (k5_xboole_0 @ sk_B @ sk_C) @ X0)))
% 4.47/4.72         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('demod', [status(thm)], ['8', '9'])).
% 4.47/4.72  thf('11', plain,
% 4.47/4.72      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 4.47/4.72         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('sup+', [status(thm)], ['2', '10'])).
% 4.47/4.72  thf('12', plain,
% 4.47/4.72      ((~ (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 4.47/4.72         <= (~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('split', [status(esa)], ['0'])).
% 4.47/4.72  thf('13', plain,
% 4.47/4.72      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 4.47/4.72       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('sup-', [status(thm)], ['11', '12'])).
% 4.47/4.72  thf(l97_xboole_1, axiom,
% 4.47/4.72    (![A:$i,B:$i]:
% 4.47/4.72     ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k5_xboole_0 @ A @ B ) ))).
% 4.47/4.72  thf('14', plain,
% 4.47/4.72      (![X2 : $i, X3 : $i]:
% 4.47/4.72         (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ (k5_xboole_0 @ X2 @ X3))),
% 4.47/4.72      inference('cnf', [status(esa)], [l97_xboole_1])).
% 4.47/4.72  thf('15', plain,
% 4.47/4.72      (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))
% 4.47/4.72         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('split', [status(esa)], ['3'])).
% 4.47/4.72  thf(t12_xboole_1, axiom,
% 4.47/4.72    (![A:$i,B:$i]:
% 4.47/4.72     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 4.47/4.72  thf('16', plain,
% 4.47/4.72      (![X6 : $i, X7 : $i]:
% 4.47/4.72         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 4.47/4.72      inference('cnf', [status(esa)], [t12_xboole_1])).
% 4.47/4.72  thf('17', plain,
% 4.47/4.72      ((((k2_xboole_0 @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))
% 4.47/4.72          = (k5_xboole_0 @ sk_B @ sk_C)))
% 4.47/4.72         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('sup-', [status(thm)], ['15', '16'])).
% 4.47/4.72  thf(t70_xboole_1, axiom,
% 4.47/4.72    (![A:$i,B:$i,C:$i]:
% 4.47/4.72     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 4.47/4.72            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 4.47/4.72       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 4.47/4.72            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 4.47/4.72  thf('18', plain,
% 4.47/4.72      (![X26 : $i, X27 : $i, X29 : $i]:
% 4.47/4.72         ((r1_xboole_0 @ X26 @ X27)
% 4.47/4.72          | ~ (r1_xboole_0 @ X26 @ (k2_xboole_0 @ X27 @ X29)))),
% 4.47/4.72      inference('cnf', [status(esa)], [t70_xboole_1])).
% 4.47/4.72  thf('19', plain,
% 4.47/4.72      ((![X0 : $i]:
% 4.47/4.72          (~ (r1_xboole_0 @ X0 @ (k5_xboole_0 @ sk_B @ sk_C))
% 4.47/4.72           | (r1_xboole_0 @ X0 @ sk_A)))
% 4.47/4.72         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('sup-', [status(thm)], ['17', '18'])).
% 4.47/4.72  thf('20', plain,
% 4.47/4.72      (((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A))
% 4.47/4.72         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('sup-', [status(thm)], ['14', '19'])).
% 4.47/4.72  thf(symmetry_r1_xboole_0, axiom,
% 4.47/4.72    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 4.47/4.72  thf('21', plain,
% 4.47/4.72      (![X0 : $i, X1 : $i]:
% 4.47/4.72         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 4.47/4.72      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 4.47/4.72  thf('22', plain,
% 4.47/4.72      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 4.47/4.72         <= (((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('sup-', [status(thm)], ['20', '21'])).
% 4.47/4.72  thf('23', plain,
% 4.47/4.72      ((~ (r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 4.47/4.72         <= (~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('split', [status(esa)], ['0'])).
% 4.47/4.72  thf('24', plain,
% 4.47/4.72      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))) | 
% 4.47/4.72       ~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('sup-', [status(thm)], ['22', '23'])).
% 4.47/4.72  thf('25', plain,
% 4.47/4.72      (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))) | 
% 4.47/4.72       ~ ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 4.47/4.72       ~ ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('split', [status(esa)], ['0'])).
% 4.47/4.72  thf('26', plain, (~ ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('sat_resolution*', [status(thm)], ['13', '24', '25'])).
% 4.47/4.72  thf('27', plain, (~ (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 4.47/4.72      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 4.47/4.72  thf('28', plain,
% 4.47/4.72      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))
% 4.47/4.72        | (r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.47/4.72  thf('29', plain,
% 4.47/4.72      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))
% 4.47/4.72         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('split', [status(esa)], ['28'])).
% 4.47/4.72  thf(t88_xboole_1, axiom,
% 4.47/4.72    (![A:$i,B:$i]:
% 4.47/4.72     ( ( r1_xboole_0 @ A @ B ) =>
% 4.47/4.72       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 4.47/4.72  thf('30', plain,
% 4.47/4.72      (![X30 : $i, X31 : $i]:
% 4.47/4.72         (((k4_xboole_0 @ (k2_xboole_0 @ X30 @ X31) @ X31) = (X30))
% 4.47/4.72          | ~ (r1_xboole_0 @ X30 @ X31))),
% 4.47/4.72      inference('cnf', [status(esa)], [t88_xboole_1])).
% 4.47/4.72  thf(t40_xboole_1, axiom,
% 4.47/4.72    (![A:$i,B:$i]:
% 4.47/4.72     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 4.47/4.72  thf('31', plain,
% 4.47/4.72      (![X18 : $i, X19 : $i]:
% 4.47/4.72         ((k4_xboole_0 @ (k2_xboole_0 @ X18 @ X19) @ X19)
% 4.47/4.72           = (k4_xboole_0 @ X18 @ X19))),
% 4.47/4.72      inference('cnf', [status(esa)], [t40_xboole_1])).
% 4.47/4.72  thf('32', plain,
% 4.47/4.72      (![X30 : $i, X31 : $i]:
% 4.47/4.72         (((k4_xboole_0 @ X30 @ X31) = (X30)) | ~ (r1_xboole_0 @ X30 @ X31))),
% 4.47/4.72      inference('demod', [status(thm)], ['30', '31'])).
% 4.47/4.72  thf('33', plain,
% 4.47/4.72      ((((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (sk_A)))
% 4.47/4.72         <= (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('sup-', [status(thm)], ['29', '32'])).
% 4.47/4.72  thf('34', plain,
% 4.47/4.72      (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))) | 
% 4.47/4.72       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('split', [status(esa)], ['28'])).
% 4.47/4.72  thf('35', plain, (((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('sat_resolution*', [status(thm)], ['13', '24', '25', '34'])).
% 4.47/4.72  thf('36', plain,
% 4.47/4.72      (((k4_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) = (sk_A))),
% 4.47/4.72      inference('simpl_trail', [status(thm)], ['33', '35'])).
% 4.47/4.72  thf('37', plain,
% 4.47/4.72      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))
% 4.47/4.72         <= (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))))),
% 4.47/4.72      inference('split', [status(esa)], ['3'])).
% 4.47/4.72  thf('38', plain,
% 4.47/4.72      (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))) | 
% 4.47/4.72       ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('split', [status(esa)], ['3'])).
% 4.47/4.72  thf('39', plain, (((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('sat_resolution*', [status(thm)], ['13', '24', '25', '38'])).
% 4.47/4.72  thf('40', plain, ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ sk_C))),
% 4.47/4.72      inference('simpl_trail', [status(thm)], ['37', '39'])).
% 4.47/4.72  thf(t33_xboole_1, axiom,
% 4.47/4.72    (![A:$i,B:$i,C:$i]:
% 4.47/4.72     ( ( r1_tarski @ A @ B ) =>
% 4.47/4.72       ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ ( k4_xboole_0 @ B @ C ) ) ))).
% 4.47/4.72  thf('41', plain,
% 4.47/4.72      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.47/4.72         (~ (r1_tarski @ X15 @ X16)
% 4.47/4.72          | (r1_tarski @ (k4_xboole_0 @ X15 @ X17) @ (k4_xboole_0 @ X16 @ X17)))),
% 4.47/4.72      inference('cnf', [status(esa)], [t33_xboole_1])).
% 4.47/4.72  thf('42', plain,
% 4.47/4.72      (![X0 : $i]:
% 4.47/4.72         (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ 
% 4.47/4.72          (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ X0))),
% 4.47/4.72      inference('sup-', [status(thm)], ['40', '41'])).
% 4.47/4.72  thf('43', plain,
% 4.47/4.72      ((r1_tarski @ sk_A @ 
% 4.47/4.72        (k4_xboole_0 @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 4.47/4.72         (k3_xboole_0 @ sk_B @ sk_C)))),
% 4.47/4.72      inference('sup+', [status(thm)], ['36', '42'])).
% 4.47/4.72  thf(l98_xboole_1, axiom,
% 4.47/4.72    (![A:$i,B:$i]:
% 4.47/4.72     ( ( k5_xboole_0 @ A @ B ) =
% 4.47/4.72       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 4.47/4.72  thf('44', plain,
% 4.47/4.72      (![X4 : $i, X5 : $i]:
% 4.47/4.72         ((k5_xboole_0 @ X4 @ X5)
% 4.47/4.72           = (k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X5)))),
% 4.47/4.72      inference('cnf', [status(esa)], [l98_xboole_1])).
% 4.47/4.72  thf('45', plain, ((r1_tarski @ sk_A @ (k5_xboole_0 @ sk_B @ sk_C))),
% 4.47/4.72      inference('demod', [status(thm)], ['43', '44'])).
% 4.47/4.72  thf('46', plain, ($false), inference('demod', [status(thm)], ['27', '45'])).
% 4.47/4.72  
% 4.47/4.72  % SZS output end Refutation
% 4.47/4.72  
% 4.54/4.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
