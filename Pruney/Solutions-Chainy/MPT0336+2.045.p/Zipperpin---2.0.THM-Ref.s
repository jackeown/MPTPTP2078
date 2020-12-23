%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kvPCPmNikm

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:26 EST 2020

% Result     : Theorem 2.52s
% Output     : Refutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   74 (  99 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  505 ( 799 expanded)
%              Number of equality atoms :   24 (  35 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

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

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
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
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ X6 @ X3 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ X10 @ X11 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,(
    r2_hidden @ sk_D_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('22',plain,(
    ! [X34: $i,X35: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X34 ) @ X35 )
      | ( r2_hidden @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X16 @ X17 ) )
      = ( k3_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X1 )
        = ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,
    ( ( k1_tarski @ sk_D_1 )
    = ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('34',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( r1_xboole_0 @ X22 @ ( k3_xboole_0 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ X25 @ X26 )
        = X25 )
      | ~ ( r1_xboole_0 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k3_xboole_0 @ sk_C_1 @ X0 ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) )
    = sk_B ),
    inference('sup+',[status(thm)],['32','37'])).

thf('39',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ~ ( r2_hidden @ ( sk_C @ sk_A @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['20','40'])).

thf('42',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['9','41'])).

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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_xboole_0 @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ X18 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_xboole_0 @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('48',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kvPCPmNikm
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:52:31 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.52/2.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.52/2.71  % Solved by: fo/fo7.sh
% 2.52/2.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.52/2.71  % done 2786 iterations in 2.257s
% 2.52/2.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.52/2.71  % SZS output start Refutation
% 2.52/2.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.52/2.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.52/2.71  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.52/2.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.52/2.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 2.52/2.71  thf(sk_A_type, type, sk_A: $i).
% 2.52/2.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.52/2.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.52/2.71  thf(sk_B_type, type, sk_B: $i).
% 2.52/2.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.52/2.71  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.52/2.71  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.52/2.71  thf(t149_zfmisc_1, conjecture,
% 2.52/2.71    (![A:$i,B:$i,C:$i,D:$i]:
% 2.52/2.71     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.52/2.71         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.52/2.71       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 2.52/2.71  thf(zf_stmt_0, negated_conjecture,
% 2.52/2.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 2.52/2.71        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 2.52/2.71            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 2.52/2.71          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 2.52/2.71    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 2.52/2.71  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf('1', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 2.52/2.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.71  thf(symmetry_r1_xboole_0, axiom,
% 2.52/2.71    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.52/2.71  thf('2', plain,
% 2.52/2.71      (![X8 : $i, X9 : $i]:
% 2.52/2.71         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 2.52/2.71      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.52/2.71  thf('3', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.52/2.71      inference('sup-', [status(thm)], ['1', '2'])).
% 2.52/2.71  thf(t4_xboole_0, axiom,
% 2.52/2.71    (![A:$i,B:$i]:
% 2.52/2.71     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 2.52/2.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.52/2.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.52/2.71            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 2.52/2.71  thf('4', plain,
% 2.52/2.71      (![X10 : $i, X11 : $i]:
% 2.52/2.71         ((r1_xboole_0 @ X10 @ X11)
% 2.52/2.71          | (r2_hidden @ (sk_C @ X11 @ X10) @ (k3_xboole_0 @ X10 @ X11)))),
% 2.52/2.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.52/2.71  thf(t48_xboole_1, axiom,
% 2.52/2.71    (![A:$i,B:$i]:
% 2.52/2.71     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 2.52/2.71  thf('5', plain,
% 2.52/2.71      (![X16 : $i, X17 : $i]:
% 2.52/2.71         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.52/2.71           = (k3_xboole_0 @ X16 @ X17))),
% 2.52/2.71      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.52/2.71  thf(d5_xboole_0, axiom,
% 2.52/2.71    (![A:$i,B:$i,C:$i]:
% 2.52/2.71     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 2.52/2.71       ( ![D:$i]:
% 2.52/2.71         ( ( r2_hidden @ D @ C ) <=>
% 2.52/2.71           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 2.52/2.71  thf('6', plain,
% 2.52/2.71      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.52/2.72         (~ (r2_hidden @ X6 @ X5)
% 2.52/2.72          | (r2_hidden @ X6 @ X3)
% 2.52/2.72          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 2.52/2.72      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.52/2.72  thf('7', plain,
% 2.52/2.72      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.52/2.72         ((r2_hidden @ X6 @ X3) | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.52/2.72      inference('simplify', [status(thm)], ['6'])).
% 2.52/2.72  thf('8', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.72         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 2.52/2.72      inference('sup-', [status(thm)], ['5', '7'])).
% 2.52/2.72  thf('9', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]:
% 2.52/2.72         ((r1_xboole_0 @ X1 @ X0) | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 2.52/2.72      inference('sup-', [status(thm)], ['4', '8'])).
% 2.52/2.72  thf('10', plain,
% 2.52/2.72      (![X10 : $i, X11 : $i]:
% 2.52/2.72         ((r1_xboole_0 @ X10 @ X11)
% 2.52/2.72          | (r2_hidden @ (sk_C @ X11 @ X10) @ (k3_xboole_0 @ X10 @ X11)))),
% 2.52/2.72      inference('cnf', [status(esa)], [t4_xboole_0])).
% 2.52/2.72  thf('11', plain,
% 2.52/2.72      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 2.52/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.72  thf(commutativity_k3_xboole_0, axiom,
% 2.52/2.72    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 2.52/2.72  thf('12', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.52/2.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.52/2.72  thf('13', plain,
% 2.52/2.72      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 2.52/2.72      inference('demod', [status(thm)], ['11', '12'])).
% 2.52/2.72  thf(t28_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i]:
% 2.52/2.72     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.52/2.72  thf('14', plain,
% 2.52/2.72      (![X14 : $i, X15 : $i]:
% 2.52/2.72         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 2.52/2.72      inference('cnf', [status(esa)], [t28_xboole_1])).
% 2.52/2.72  thf('15', plain,
% 2.52/2.72      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))
% 2.52/2.72         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.52/2.72      inference('sup-', [status(thm)], ['13', '14'])).
% 2.52/2.72  thf('16', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.52/2.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.52/2.72  thf('17', plain,
% 2.52/2.72      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A))
% 2.52/2.72         = (k3_xboole_0 @ sk_B @ sk_A))),
% 2.52/2.72      inference('demod', [status(thm)], ['15', '16'])).
% 2.52/2.72  thf('18', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.72         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r2_hidden @ X2 @ X1))),
% 2.52/2.72      inference('sup-', [status(thm)], ['5', '7'])).
% 2.52/2.72  thf('19', plain,
% 2.52/2.72      (![X0 : $i]:
% 2.52/2.72         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 2.52/2.72          | (r2_hidden @ X0 @ (k1_tarski @ sk_D_1)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['17', '18'])).
% 2.52/2.72  thf('20', plain,
% 2.52/2.72      (((r1_xboole_0 @ sk_B @ sk_A)
% 2.52/2.72        | (r2_hidden @ (sk_C @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['10', '19'])).
% 2.52/2.72  thf('21', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 2.52/2.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.72  thf(l27_zfmisc_1, axiom,
% 2.52/2.72    (![A:$i,B:$i]:
% 2.52/2.72     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 2.52/2.72  thf('22', plain,
% 2.52/2.72      (![X34 : $i, X35 : $i]:
% 2.52/2.72         ((r1_xboole_0 @ (k1_tarski @ X34) @ X35) | (r2_hidden @ X34 @ X35))),
% 2.52/2.72      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 2.52/2.72  thf(t83_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i]:
% 2.52/2.72     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 2.52/2.72  thf('23', plain,
% 2.52/2.72      (![X25 : $i, X26 : $i]:
% 2.52/2.72         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 2.52/2.72      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.52/2.72  thf('24', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]:
% 2.52/2.72         ((r2_hidden @ X1 @ X0)
% 2.52/2.72          | ((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['22', '23'])).
% 2.52/2.72  thf('25', plain,
% 2.52/2.72      (![X16 : $i, X17 : $i]:
% 2.52/2.72         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X16 @ X17))
% 2.52/2.72           = (k3_xboole_0 @ X16 @ X17))),
% 2.52/2.72      inference('cnf', [status(esa)], [t48_xboole_1])).
% 2.52/2.72  thf('26', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]:
% 2.52/2.72         (((k1_tarski @ X0) = (k3_xboole_0 @ (k1_tarski @ X0) @ X1))
% 2.52/2.72          | (r2_hidden @ X0 @ (k4_xboole_0 @ (k1_tarski @ X0) @ X1)))),
% 2.52/2.72      inference('sup+', [status(thm)], ['24', '25'])).
% 2.52/2.72  thf('27', plain,
% 2.52/2.72      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 2.52/2.72         (~ (r2_hidden @ X6 @ X5)
% 2.52/2.72          | ~ (r2_hidden @ X6 @ X4)
% 2.52/2.72          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 2.52/2.72      inference('cnf', [status(esa)], [d5_xboole_0])).
% 2.52/2.72  thf('28', plain,
% 2.52/2.72      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.52/2.72         (~ (r2_hidden @ X6 @ X4)
% 2.52/2.72          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.52/2.72      inference('simplify', [status(thm)], ['27'])).
% 2.52/2.72  thf('29', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]:
% 2.52/2.72         (((k1_tarski @ X1) = (k3_xboole_0 @ (k1_tarski @ X1) @ X0))
% 2.52/2.72          | ~ (r2_hidden @ X1 @ X0))),
% 2.52/2.72      inference('sup-', [status(thm)], ['26', '28'])).
% 2.52/2.72  thf('30', plain,
% 2.52/2.72      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ (k1_tarski @ sk_D_1) @ sk_C_1))),
% 2.52/2.72      inference('sup-', [status(thm)], ['21', '29'])).
% 2.52/2.72  thf('31', plain,
% 2.52/2.72      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 2.52/2.72      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 2.52/2.72  thf('32', plain,
% 2.52/2.72      (((k1_tarski @ sk_D_1) = (k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_D_1)))),
% 2.52/2.72      inference('demod', [status(thm)], ['30', '31'])).
% 2.52/2.72  thf('33', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 2.52/2.72      inference('sup-', [status(thm)], ['1', '2'])).
% 2.52/2.72  thf(t74_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i,C:$i]:
% 2.52/2.72     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 2.52/2.72          ( r1_xboole_0 @ A @ B ) ) ))).
% 2.52/2.72  thf('34', plain,
% 2.52/2.72      (![X22 : $i, X23 : $i, X24 : $i]:
% 2.52/2.72         (~ (r1_xboole_0 @ X22 @ X23)
% 2.52/2.72          | (r1_xboole_0 @ X22 @ (k3_xboole_0 @ X23 @ X24)))),
% 2.52/2.72      inference('cnf', [status(esa)], [t74_xboole_1])).
% 2.52/2.72  thf('35', plain,
% 2.52/2.72      (![X0 : $i]: (r1_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0))),
% 2.52/2.72      inference('sup-', [status(thm)], ['33', '34'])).
% 2.52/2.72  thf('36', plain,
% 2.52/2.72      (![X25 : $i, X26 : $i]:
% 2.52/2.72         (((k4_xboole_0 @ X25 @ X26) = (X25)) | ~ (r1_xboole_0 @ X25 @ X26))),
% 2.52/2.72      inference('cnf', [status(esa)], [t83_xboole_1])).
% 2.52/2.72  thf('37', plain,
% 2.52/2.72      (![X0 : $i]:
% 2.52/2.72         ((k4_xboole_0 @ sk_B @ (k3_xboole_0 @ sk_C_1 @ X0)) = (sk_B))),
% 2.52/2.72      inference('sup-', [status(thm)], ['35', '36'])).
% 2.52/2.72  thf('38', plain, (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)) = (sk_B))),
% 2.52/2.72      inference('sup+', [status(thm)], ['32', '37'])).
% 2.52/2.72  thf('39', plain,
% 2.52/2.72      (![X3 : $i, X4 : $i, X6 : $i]:
% 2.52/2.72         (~ (r2_hidden @ X6 @ X4)
% 2.52/2.72          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 2.52/2.72      inference('simplify', [status(thm)], ['27'])).
% 2.52/2.72  thf('40', plain,
% 2.52/2.72      (![X0 : $i]:
% 2.52/2.72         (~ (r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_D_1)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['38', '39'])).
% 2.52/2.72  thf('41', plain,
% 2.52/2.72      (((r1_xboole_0 @ sk_B @ sk_A)
% 2.52/2.72        | ~ (r2_hidden @ (sk_C @ sk_A @ sk_B) @ sk_B))),
% 2.52/2.72      inference('sup-', [status(thm)], ['20', '40'])).
% 2.52/2.72  thf('42', plain,
% 2.52/2.72      (((r1_xboole_0 @ sk_B @ sk_A) | (r1_xboole_0 @ sk_B @ sk_A))),
% 2.52/2.72      inference('sup-', [status(thm)], ['9', '41'])).
% 2.52/2.72  thf('43', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.52/2.72      inference('simplify', [status(thm)], ['42'])).
% 2.52/2.72  thf(t70_xboole_1, axiom,
% 2.52/2.72    (![A:$i,B:$i,C:$i]:
% 2.52/2.72     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 2.52/2.72            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 2.52/2.72       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 2.52/2.72            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 2.52/2.72  thf('44', plain,
% 2.52/2.72      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.52/2.72         ((r1_xboole_0 @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 2.52/2.72          | ~ (r1_xboole_0 @ X18 @ X19)
% 2.52/2.72          | ~ (r1_xboole_0 @ X18 @ X20))),
% 2.52/2.72      inference('cnf', [status(esa)], [t70_xboole_1])).
% 2.52/2.72  thf('45', plain,
% 2.52/2.72      (![X0 : $i]:
% 2.52/2.72         (~ (r1_xboole_0 @ sk_B @ X0)
% 2.52/2.72          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ X0)))),
% 2.52/2.72      inference('sup-', [status(thm)], ['43', '44'])).
% 2.52/2.72  thf('46', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_A @ sk_C_1))),
% 2.52/2.72      inference('sup-', [status(thm)], ['3', '45'])).
% 2.52/2.72  thf('47', plain,
% 2.52/2.72      (![X8 : $i, X9 : $i]:
% 2.52/2.72         ((r1_xboole_0 @ X8 @ X9) | ~ (r1_xboole_0 @ X9 @ X8))),
% 2.52/2.72      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.52/2.72  thf('48', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 2.52/2.72      inference('sup-', [status(thm)], ['46', '47'])).
% 2.52/2.72  thf('49', plain, ($false), inference('demod', [status(thm)], ['0', '48'])).
% 2.52/2.72  
% 2.52/2.72  % SZS output end Refutation
% 2.52/2.72  
% 2.54/2.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
