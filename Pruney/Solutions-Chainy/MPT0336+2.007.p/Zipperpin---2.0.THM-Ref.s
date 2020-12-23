%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1XRRArfgSa

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:20 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 103 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  472 ( 783 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('0',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X37 ) @ X38 )
      | ( r2_hidden @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k3_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

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
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X24 @ X25 )
        = X24 )
      | ~ ( r1_tarski @ X24 @ X25 ) ) ),
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

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ X21 )
      = ( k3_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_D_1 ) ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ sk_A @ k1_xboole_0 )
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X26: $i] :
      ( r1_xboole_0 @ X26 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k3_xboole_0 @ X10 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ sk_D_1 @ sk_B )
    | ( r1_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ sk_B @ sk_A )
    | ( r2_hidden @ sk_D_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('24',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('25',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( r1_xboole_0 @ X27 @ ( k2_xboole_0 @ X28 @ X29 ) )
      | ~ ( r1_xboole_0 @ X27 @ X28 )
      | ~ ( r1_xboole_0 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_B @ X0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_B )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('29',plain,
    ( ( r2_hidden @ sk_D_1 @ sk_B )
    | ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_C_1 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('32',plain,(
    ~ ( r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ sk_D_1 @ sk_B ),
    inference(clc,[status(thm)],['29','32'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['33','37'])).

thf('39',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('40',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('41',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r2_hidden @ sk_D_1 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('44',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k3_xboole_0 @ X15 @ X18 ) )
      | ~ ( r1_xboole_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('47',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference('sup-',[status(thm)],['42','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1XRRArfgSa
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.60/0.80  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.80  % Solved by: fo/fo7.sh
% 0.60/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.80  % done 658 iterations in 0.361s
% 0.60/0.80  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.80  % SZS output start Refutation
% 0.60/0.80  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.80  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.60/0.80  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.60/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.80  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.80  thf(l27_zfmisc_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.60/0.80  thf('0', plain,
% 0.60/0.80      (![X37 : $i, X38 : $i]:
% 0.60/0.80         ((r1_xboole_0 @ (k1_tarski @ X37) @ X38) | (r2_hidden @ X37 @ X38))),
% 0.60/0.80      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.60/0.80  thf(symmetry_r1_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.60/0.80  thf('1', plain,
% 0.60/0.80      (![X13 : $i, X14 : $i]:
% 0.60/0.80         ((r1_xboole_0 @ X13 @ X14) | ~ (r1_xboole_0 @ X14 @ X13))),
% 0.60/0.80      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.60/0.80  thf('2', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.60/0.80  thf(d7_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.60/0.80       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.80  thf('3', plain,
% 0.60/0.80      (![X10 : $i, X11 : $i]:
% 0.60/0.80         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 0.60/0.80          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.60/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.80  thf('4', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]:
% 0.60/0.80         ((r2_hidden @ X0 @ X1)
% 0.60/0.80          | ((k3_xboole_0 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.80  thf(t149_zfmisc_1, conjecture,
% 0.60/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.80     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.60/0.80         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.60/0.80       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.60/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.80    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.80        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.60/0.80            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.60/0.80          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.60/0.80    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.60/0.80  thf('5', plain,
% 0.60/0.80      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(commutativity_k3_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.60/0.80  thf('6', plain,
% 0.60/0.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.80  thf('7', plain,
% 0.60/0.80      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))),
% 0.60/0.80      inference('demod', [status(thm)], ['5', '6'])).
% 0.60/0.80  thf(t28_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.60/0.80  thf('8', plain,
% 0.60/0.80      (![X24 : $i, X25 : $i]:
% 0.60/0.80         (((k3_xboole_0 @ X24 @ X25) = (X24)) | ~ (r1_tarski @ X24 @ X25))),
% 0.60/0.80      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.80  thf('9', plain,
% 0.60/0.80      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D_1))
% 0.60/0.80         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.60/0.80      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.80  thf('10', plain,
% 0.60/0.80      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.80  thf(t16_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.60/0.80       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.60/0.80  thf('11', plain,
% 0.60/0.80      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.80         ((k3_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ X21)
% 0.60/0.80           = (k3_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21)))),
% 0.60/0.80      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.60/0.80  thf('12', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.80         ((k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.60/0.80           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.60/0.80      inference('sup+', [status(thm)], ['10', '11'])).
% 0.60/0.80  thf('13', plain,
% 0.60/0.80      (((k3_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_D_1)))
% 0.60/0.80         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.60/0.80      inference('demod', [status(thm)], ['9', '12'])).
% 0.60/0.80  thf('14', plain,
% 0.60/0.80      ((((k3_xboole_0 @ sk_A @ k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.60/0.80        | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.60/0.80      inference('sup+', [status(thm)], ['4', '13'])).
% 0.60/0.80  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.60/0.80  thf('15', plain, (![X26 : $i]: (r1_xboole_0 @ X26 @ k1_xboole_0)),
% 0.60/0.80      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.60/0.80  thf('16', plain,
% 0.60/0.80      (![X10 : $i, X11 : $i]:
% 0.60/0.80         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 0.60/0.80          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.60/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.80  thf('17', plain,
% 0.60/0.80      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['15', '16'])).
% 0.60/0.80  thf('18', plain,
% 0.60/0.80      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.60/0.80        | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.60/0.80      inference('demod', [status(thm)], ['14', '17'])).
% 0.60/0.80  thf('19', plain,
% 0.60/0.80      (![X10 : $i, X12 : $i]:
% 0.60/0.80         ((r1_xboole_0 @ X10 @ X12)
% 0.60/0.80          | ((k3_xboole_0 @ X10 @ X12) != (k1_xboole_0)))),
% 0.60/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.80  thf('20', plain,
% 0.60/0.80      ((((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.80        | (r2_hidden @ sk_D_1 @ sk_B)
% 0.60/0.80        | (r1_xboole_0 @ sk_B @ sk_A))),
% 0.60/0.80      inference('sup-', [status(thm)], ['18', '19'])).
% 0.60/0.80  thf('21', plain,
% 0.60/0.80      (((r1_xboole_0 @ sk_B @ sk_A) | (r2_hidden @ sk_D_1 @ sk_B))),
% 0.60/0.80      inference('simplify', [status(thm)], ['20'])).
% 0.60/0.80  thf('22', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf('23', plain,
% 0.60/0.80      (![X13 : $i, X14 : $i]:
% 0.60/0.80         ((r1_xboole_0 @ X13 @ X14) | ~ (r1_xboole_0 @ X14 @ X13))),
% 0.60/0.80      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.60/0.80  thf('24', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.60/0.80      inference('sup-', [status(thm)], ['22', '23'])).
% 0.60/0.80  thf(t70_xboole_1, axiom,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.60/0.80            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.60/0.80       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.60/0.80            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.60/0.80  thf('25', plain,
% 0.60/0.80      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.60/0.80         ((r1_xboole_0 @ X27 @ (k2_xboole_0 @ X28 @ X29))
% 0.60/0.80          | ~ (r1_xboole_0 @ X27 @ X28)
% 0.60/0.80          | ~ (r1_xboole_0 @ X27 @ X29))),
% 0.60/0.80      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.60/0.80  thf('26', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (r1_xboole_0 @ sk_B @ X0)
% 0.60/0.80          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['24', '25'])).
% 0.60/0.80  thf('27', plain,
% 0.60/0.80      (((r2_hidden @ sk_D_1 @ sk_B)
% 0.60/0.80        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['21', '26'])).
% 0.60/0.80  thf('28', plain,
% 0.60/0.80      (![X13 : $i, X14 : $i]:
% 0.60/0.80         ((r1_xboole_0 @ X13 @ X14) | ~ (r1_xboole_0 @ X14 @ X13))),
% 0.60/0.80      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.60/0.80  thf('29', plain,
% 0.60/0.80      (((r2_hidden @ sk_D_1 @ sk_B)
% 0.60/0.80        | (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B))),
% 0.60/0.80      inference('sup-', [status(thm)], ['27', '28'])).
% 0.60/0.80  thf('30', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(commutativity_k2_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.60/0.80  thf('31', plain,
% 0.60/0.80      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.80      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.80  thf('32', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.60/0.80      inference('demod', [status(thm)], ['30', '31'])).
% 0.60/0.80  thf('33', plain, ((r2_hidden @ sk_D_1 @ sk_B)),
% 0.60/0.80      inference('clc', [status(thm)], ['29', '32'])).
% 0.60/0.80  thf('34', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 0.60/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.80  thf(d4_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i,C:$i]:
% 0.60/0.80     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.60/0.80       ( ![D:$i]:
% 0.60/0.80         ( ( r2_hidden @ D @ C ) <=>
% 0.60/0.80           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.60/0.80  thf('35', plain,
% 0.60/0.80      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.80         (~ (r2_hidden @ X4 @ X5)
% 0.60/0.80          | ~ (r2_hidden @ X4 @ X6)
% 0.60/0.80          | (r2_hidden @ X4 @ X7)
% 0.60/0.80          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.60/0.80      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.60/0.80  thf('36', plain,
% 0.60/0.80      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.60/0.80         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 0.60/0.80          | ~ (r2_hidden @ X4 @ X6)
% 0.60/0.80          | ~ (r2_hidden @ X4 @ X5))),
% 0.60/0.80      inference('simplify', [status(thm)], ['35'])).
% 0.60/0.80  thf('37', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (r2_hidden @ sk_D_1 @ X0)
% 0.60/0.80          | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ X0 @ sk_C_1)))),
% 0.60/0.80      inference('sup-', [status(thm)], ['34', '36'])).
% 0.60/0.80  thf('38', plain, ((r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_C_1))),
% 0.60/0.80      inference('sup-', [status(thm)], ['33', '37'])).
% 0.60/0.80  thf('39', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.60/0.80      inference('sup-', [status(thm)], ['22', '23'])).
% 0.60/0.80  thf('40', plain,
% 0.60/0.80      (![X10 : $i, X11 : $i]:
% 0.60/0.80         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 0.60/0.80          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.60/0.80      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.80  thf('41', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['39', '40'])).
% 0.60/0.80  thf('42', plain, ((r2_hidden @ sk_D_1 @ k1_xboole_0)),
% 0.60/0.80      inference('demod', [status(thm)], ['38', '41'])).
% 0.60/0.80  thf('43', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.60/0.80      inference('sup-', [status(thm)], ['39', '40'])).
% 0.60/0.80  thf(t4_xboole_0, axiom,
% 0.60/0.80    (![A:$i,B:$i]:
% 0.60/0.80     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.80            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.80       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.60/0.80            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.60/0.80  thf('44', plain,
% 0.60/0.80      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.60/0.80         (~ (r2_hidden @ X17 @ (k3_xboole_0 @ X15 @ X18))
% 0.60/0.80          | ~ (r1_xboole_0 @ X15 @ X18))),
% 0.60/0.80      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.60/0.80  thf('45', plain,
% 0.60/0.80      (![X0 : $i]:
% 0.60/0.80         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.60/0.80      inference('sup-', [status(thm)], ['43', '44'])).
% 0.60/0.80  thf('46', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.60/0.80      inference('sup-', [status(thm)], ['22', '23'])).
% 0.60/0.80  thf('47', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.60/0.80      inference('demod', [status(thm)], ['45', '46'])).
% 0.60/0.80  thf('48', plain, ($false), inference('sup-', [status(thm)], ['42', '47'])).
% 0.60/0.80  
% 0.60/0.80  % SZS output end Refutation
% 0.60/0.80  
% 0.60/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
