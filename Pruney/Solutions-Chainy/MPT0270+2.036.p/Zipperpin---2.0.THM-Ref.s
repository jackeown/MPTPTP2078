%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h5EIhHEDIq

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 154 expanded)
%              Number of leaves         :   20 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  656 (1400 expanded)
%              Number of equality atoms :   53 ( 113 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('5',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,
    ( ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('10',plain,(
    ! [X29: $i,X30: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X29 ) @ X30 )
      | ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k4_xboole_0 @ X16 @ X17 )
        = X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) )
      | ~ ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X10 )
      | ~ ( r2_hidden @ X8 @ ( k5_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

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
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_B @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','27'])).

thf('29',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_A @ X0 )
        | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ X0 @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('32',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('34',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ( r2_hidden @ sk_A @ ( k3_xboole_0 @ sk_B_1 @ ( k1_tarski @ sk_A ) ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','25'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( ( k1_tarski @ sk_A )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) )
   <= ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,
    ( ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
      | ( ( k1_tarski @ sk_A )
        = k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('41',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( X31 != X33 )
      | ~ ( r2_hidden @ X31 @ ( k4_xboole_0 @ X32 @ ( k1_tarski @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('43',plain,(
    ! [X32: $i,X33: $i] :
      ~ ( r2_hidden @ X33 @ ( k4_xboole_0 @ X32 @ ( k1_tarski @ X33 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('45',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ sk_A @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['8'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('50',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ sk_A @ sk_B_1 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
     != ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_B_1 ) ),
    inference(split,[status(esa)],['8'])).

thf('54',plain,
    ( ( r2_hidden @ sk_A @ sk_B_1 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','47','48','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.h5EIhHEDIq
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:28:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.56  % Solved by: fo/fo7.sh
% 0.21/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.56  % done 175 iterations in 0.099s
% 0.21/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.56  % SZS output start Refutation
% 0.21/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.56  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.56  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.56  thf(t67_zfmisc_1, conjecture,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.56       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.21/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.56    (~( ![A:$i,B:$i]:
% 0.21/0.56        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.21/0.56          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.21/0.56    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.21/0.56  thf('0', plain,
% 0.21/0.56      (((r2_hidden @ sk_A @ sk_B_1)
% 0.21/0.56        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('1', plain,
% 0.21/0.56      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.21/0.56       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('2', plain,
% 0.21/0.56      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf('3', plain,
% 0.21/0.56      (((r2_hidden @ sk_A @ sk_B_1)) <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('split', [status(esa)], ['0'])).
% 0.21/0.56  thf(d4_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.21/0.56       ( ![D:$i]:
% 0.21/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.56           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.21/0.56  thf('4', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.56          | ~ (r2_hidden @ X2 @ X4)
% 0.21/0.56          | (r2_hidden @ X2 @ X5)
% 0.21/0.56          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.56  thf('5', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.56         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.21/0.56          | ~ (r2_hidden @ X2 @ X4)
% 0.21/0.56          | ~ (r2_hidden @ X2 @ X3))),
% 0.21/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.56  thf('6', plain,
% 0.21/0.56      ((![X0 : $i]:
% 0.21/0.56          (~ (r2_hidden @ sk_A @ X0)
% 0.21/0.56           | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B_1))))
% 0.21/0.56         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.56  thf('7', plain,
% 0.21/0.56      (((r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B_1 @ sk_B_1)))
% 0.21/0.56         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['2', '6'])).
% 0.21/0.56  thf('8', plain,
% 0.21/0.56      ((~ (r2_hidden @ sk_A @ sk_B_1)
% 0.21/0.56        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.21/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.56  thf('9', plain,
% 0.21/0.56      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))
% 0.21/0.56         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.21/0.56      inference('split', [status(esa)], ['8'])).
% 0.21/0.56  thf(l27_zfmisc_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.21/0.56  thf('10', plain,
% 0.21/0.56      (![X29 : $i, X30 : $i]:
% 0.21/0.56         ((r1_xboole_0 @ (k1_tarski @ X29) @ X30) | (r2_hidden @ X29 @ X30))),
% 0.21/0.56      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.21/0.56  thf(t83_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.56  thf('11', plain,
% 0.21/0.56      (![X16 : $i, X17 : $i]:
% 0.21/0.56         (((k4_xboole_0 @ X16 @ X17) = (X16)) | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.21/0.56      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.56  thf('12', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         ((r2_hidden @ X1 @ X0)
% 0.21/0.56          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.56  thf(t7_xboole_0, axiom,
% 0.21/0.56    (![A:$i]:
% 0.21/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.56  thf('13', plain,
% 0.21/0.56      (![X12 : $i]:
% 0.21/0.56         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.56  thf('14', plain,
% 0.21/0.56      (![X12 : $i]:
% 0.21/0.56         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.56  thf('15', plain,
% 0.21/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.56         ((r2_hidden @ X2 @ (k3_xboole_0 @ X3 @ X4))
% 0.21/0.56          | ~ (r2_hidden @ X2 @ X4)
% 0.21/0.56          | ~ (r2_hidden @ X2 @ X3))),
% 0.21/0.56      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.56  thf('16', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]:
% 0.21/0.56         (((X0) = (k1_xboole_0))
% 0.21/0.56          | ~ (r2_hidden @ (sk_B @ X0) @ X1)
% 0.21/0.56          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X1 @ X0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.56  thf('17', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         (((X0) = (k1_xboole_0))
% 0.21/0.56          | (r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.21/0.56          | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('sup-', [status(thm)], ['13', '16'])).
% 0.21/0.56  thf('18', plain,
% 0.21/0.56      (![X0 : $i]:
% 0.21/0.56         ((r2_hidden @ (sk_B @ X0) @ (k3_xboole_0 @ X0 @ X0))
% 0.21/0.56          | ((X0) = (k1_xboole_0)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.56  thf(t100_xboole_1, axiom,
% 0.21/0.56    (![A:$i,B:$i]:
% 0.21/0.56     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.56  thf('19', plain,
% 0.21/0.56      (![X13 : $i, X14 : $i]:
% 0.21/0.56         ((k4_xboole_0 @ X13 @ X14)
% 0.21/0.56           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.56  thf(t1_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i,C:$i]:
% 0.21/0.56     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.21/0.56       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.21/0.56  thf('20', plain,
% 0.21/0.56      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X8 @ X9)
% 0.21/0.56          | ~ (r2_hidden @ X8 @ X10)
% 0.21/0.56          | ~ (r2_hidden @ X8 @ (k5_xboole_0 @ X9 @ X10)))),
% 0.21/0.56      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.21/0.56  thf('21', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 0.21/0.56          | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.56          | ~ (r2_hidden @ X2 @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.56  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.56    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.56  thf('22', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.56      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.56  thf('23', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X6 @ X5)
% 0.21/0.56          | (r2_hidden @ X6 @ X4)
% 0.21/0.56          | ((X5) != (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.56      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.21/0.56  thf('24', plain,
% 0.21/0.56      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.21/0.56         ((r2_hidden @ X6 @ X4) | ~ (r2_hidden @ X6 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.21/0.56      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.56  thf('25', plain,
% 0.21/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.56         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 0.21/0.56      inference('sup-', [status(thm)], ['22', '24'])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.57          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('clc', [status(thm)], ['21', '25'])).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((X0) = (k1_xboole_0))
% 0.21/0.57          | ~ (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['18', '26'])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (~ (r2_hidden @ (sk_B @ (k1_tarski @ X0)) @ (k1_tarski @ X0))
% 0.21/0.57          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.21/0.57          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['12', '27'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      (![X12 : $i]:
% 0.21/0.57         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 0.21/0.57      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.57          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.57      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          (~ (r2_hidden @ sk_A @ X0)
% 0.21/0.57           | (r2_hidden @ sk_A @ (k3_xboole_0 @ X0 @ sk_B_1))))
% 0.21/0.57         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['3', '5'])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.57         | (r2_hidden @ sk_A @ (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))
% 0.21/0.57         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.57         | (r2_hidden @ sk_A @ (k3_xboole_0 @ sk_B_1 @ (k1_tarski @ sk_A)))))
% 0.21/0.57         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.57      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.57          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.21/0.57      inference('clc', [status(thm)], ['21', '25'])).
% 0.21/0.57  thf('37', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.21/0.57          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.57  thf('38', plain,
% 0.21/0.57      (((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.21/0.57         | ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1))))
% 0.21/0.57         <= (((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['34', '37'])).
% 0.21/0.57  thf('39', plain,
% 0.21/0.57      (((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))
% 0.21/0.57         | ((k1_tarski @ sk_A) = (k1_xboole_0))))
% 0.21/0.57         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.21/0.57             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['9', '38'])).
% 0.21/0.57  thf('40', plain,
% 0.21/0.57      (![X0 : $i]:
% 0.21/0.57         (((k1_tarski @ X0) = (k1_xboole_0))
% 0.21/0.57          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.21/0.57      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('41', plain,
% 0.21/0.57      ((((k1_tarski @ sk_A) = (k1_xboole_0)))
% 0.21/0.57         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.21/0.57             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('clc', [status(thm)], ['39', '40'])).
% 0.21/0.57  thf(t64_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.21/0.57       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.21/0.57  thf('42', plain,
% 0.21/0.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.57         (((X31) != (X33))
% 0.21/0.57          | ~ (r2_hidden @ X31 @ (k4_xboole_0 @ X32 @ (k1_tarski @ X33))))),
% 0.21/0.57      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.21/0.57  thf('43', plain,
% 0.21/0.57      (![X32 : $i, X33 : $i]:
% 0.21/0.57         ~ (r2_hidden @ X33 @ (k4_xboole_0 @ X32 @ (k1_tarski @ X33)))),
% 0.21/0.57      inference('simplify', [status(thm)], ['42'])).
% 0.21/0.57  thf('44', plain,
% 0.21/0.57      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ (k4_xboole_0 @ X0 @ k1_xboole_0)))
% 0.21/0.57         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.21/0.57             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['41', '43'])).
% 0.21/0.57  thf(t3_boole, axiom,
% 0.21/0.57    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.57  thf('45', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.21/0.57      inference('cnf', [status(esa)], [t3_boole])).
% 0.21/0.57  thf('46', plain,
% 0.21/0.57      ((![X0 : $i]: ~ (r2_hidden @ sk_A @ X0))
% 0.21/0.57         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))) & 
% 0.21/0.57             ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('demod', [status(thm)], ['44', '45'])).
% 0.21/0.57  thf('47', plain,
% 0.21/0.57      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.21/0.57       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '46'])).
% 0.21/0.57  thf('48', plain,
% 0.21/0.57      (~ ((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.21/0.57       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.21/0.57      inference('split', [status(esa)], ['8'])).
% 0.21/0.57  thf('49', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         ((r2_hidden @ X1 @ X0)
% 0.21/0.57          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf('50', plain,
% 0.21/0.57      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) != (k1_tarski @ sk_A)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf('51', plain,
% 0.21/0.57      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.21/0.57         | (r2_hidden @ sk_A @ sk_B_1)))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.21/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.21/0.57  thf('52', plain,
% 0.21/0.57      (((r2_hidden @ sk_A @ sk_B_1))
% 0.21/0.57         <= (~
% 0.21/0.57             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A))))),
% 0.21/0.57      inference('simplify', [status(thm)], ['51'])).
% 0.21/0.57  thf('53', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_A @ sk_B_1)) <= (~ ((r2_hidden @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['8'])).
% 0.21/0.57  thf('54', plain,
% 0.21/0.57      (((r2_hidden @ sk_A @ sk_B_1)) | 
% 0.21/0.57       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B_1) = (k1_tarski @ sk_A)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['52', '53'])).
% 0.21/0.57  thf('55', plain, ($false),
% 0.21/0.57      inference('sat_resolution*', [status(thm)], ['1', '47', '48', '54'])).
% 0.21/0.57  
% 0.21/0.57  % SZS output end Refutation
% 0.21/0.57  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
