%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sA0yAuASip

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:21 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :   74 (  99 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  481 ( 766 expanded)
%              Number of equality atoms :   32 (  38 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('3',plain,(
    ! [X31: $i] :
      ( ( k2_tarski @ X31 @ X31 )
      = ( k1_tarski @ X31 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('4',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ X37 @ X38 )
      | ( r1_xboole_0 @ ( k2_tarski @ X37 @ X39 ) @ X38 )
      | ( r2_hidden @ X39 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k3_xboole_0 @ X21 @ X22 )
        = X21 )
      | ~ ( r1_tarski @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D_1 ) )
    = ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('13',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('14',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D_1 ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','12','13','14'])).

thf('16',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['8','15'])).

thf('17',plain,(
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

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ( r2_hidden @ X4 @ X7 )
      | ( X7
       != ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('19',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X4 @ ( k3_xboole_0 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X4 @ X6 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_D_1 @ X0 )
      | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D_1 @ ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('23',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ( r1_xboole_0 @ X23 @ ( k3_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ sk_B @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ sk_A ) )
    | ( r2_hidden @ sk_D_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('31',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('34',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k3_xboole_0 @ X15 @ X18 ) )
      | ~ ( r1_xboole_0 @ X15 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['28','37'])).

thf('39',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t78_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
        = ( k3_xboole_0 @ A @ C ) ) ) )).

thf('40',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ X26 @ X27 )
      | ( ( k3_xboole_0 @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) )
        = ( k3_xboole_0 @ X26 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[t78_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k3_xboole_0 @ X10 @ X12 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ sk_B @ X0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('47',plain,(
    r1_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    $false ),
    inference(demod,[status(thm)],['2','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sA0yAuASip
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.82  % Solved by: fo/fo7.sh
% 0.60/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.82  % done 741 iterations in 0.384s
% 0.60/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.82  % SZS output start Refutation
% 0.60/0.82  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.60/0.82  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.60/0.82  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.60/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.82  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.60/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.60/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.60/0.82  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.60/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.82  thf(t149_zfmisc_1, conjecture,
% 0.60/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.82     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.60/0.82         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.60/0.82       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.60/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.82    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.82        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 0.60/0.82            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 0.60/0.82          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 0.60/0.82    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 0.60/0.82  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_1) @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(commutativity_k2_xboole_0, axiom,
% 0.60/0.82    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.60/0.82  thf('1', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.60/0.82      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.60/0.82  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.60/0.82      inference('demod', [status(thm)], ['0', '1'])).
% 0.60/0.82  thf(t69_enumset1, axiom,
% 0.60/0.82    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.60/0.82  thf('3', plain, (![X31 : $i]: ((k2_tarski @ X31 @ X31) = (k1_tarski @ X31))),
% 0.60/0.82      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.60/0.82  thf(t57_zfmisc_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 0.60/0.82          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 0.60/0.82  thf('4', plain,
% 0.60/0.82      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.60/0.82         ((r2_hidden @ X37 @ X38)
% 0.60/0.82          | (r1_xboole_0 @ (k2_tarski @ X37 @ X39) @ X38)
% 0.60/0.82          | (r2_hidden @ X39 @ X38))),
% 0.60/0.82      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 0.60/0.82  thf('5', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 0.60/0.82          | (r2_hidden @ X0 @ X1)
% 0.60/0.82          | (r2_hidden @ X0 @ X1))),
% 0.60/0.82      inference('sup+', [status(thm)], ['3', '4'])).
% 0.60/0.82  thf('6', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.60/0.82      inference('simplify', [status(thm)], ['5'])).
% 0.60/0.82  thf(d7_xboole_0, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.60/0.82       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.82  thf('7', plain,
% 0.60/0.82      (![X10 : $i, X11 : $i]:
% 0.60/0.82         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 0.60/0.82          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.60/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.82  thf('8', plain,
% 0.60/0.82      (![X0 : $i, X1 : $i]:
% 0.60/0.82         ((r2_hidden @ X1 @ X0)
% 0.60/0.82          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.82  thf('9', plain,
% 0.60/0.82      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(t28_xboole_1, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.60/0.82  thf('10', plain,
% 0.60/0.82      (![X21 : $i, X22 : $i]:
% 0.60/0.82         (((k3_xboole_0 @ X21 @ X22) = (X21)) | ~ (r1_tarski @ X21 @ X22))),
% 0.60/0.82      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.60/0.82  thf('11', plain,
% 0.60/0.82      (((k3_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D_1))
% 0.60/0.82         = (k3_xboole_0 @ sk_A @ sk_B))),
% 0.60/0.82      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.82  thf(commutativity_k3_xboole_0, axiom,
% 0.60/0.82    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.60/0.82  thf('12', plain,
% 0.60/0.82      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.82  thf('13', plain,
% 0.60/0.82      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.82  thf('14', plain,
% 0.60/0.82      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.82  thf('15', plain,
% 0.60/0.82      (((k3_xboole_0 @ (k1_tarski @ sk_D_1) @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.60/0.82         = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.60/0.82      inference('demod', [status(thm)], ['11', '12', '13', '14'])).
% 0.60/0.82  thf('16', plain,
% 0.60/0.82      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.60/0.82        | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 0.60/0.82      inference('sup+', [status(thm)], ['8', '15'])).
% 0.60/0.82  thf('17', plain, ((r2_hidden @ sk_D_1 @ sk_C_1)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(d4_xboole_0, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.60/0.82       ( ![D:$i]:
% 0.60/0.82         ( ( r2_hidden @ D @ C ) <=>
% 0.60/0.82           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.60/0.82  thf('18', plain,
% 0.60/0.82      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X4 @ X5)
% 0.60/0.82          | ~ (r2_hidden @ X4 @ X6)
% 0.60/0.82          | (r2_hidden @ X4 @ X7)
% 0.60/0.82          | ((X7) != (k3_xboole_0 @ X5 @ X6)))),
% 0.60/0.82      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.60/0.82  thf('19', plain,
% 0.60/0.82      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.60/0.82         ((r2_hidden @ X4 @ (k3_xboole_0 @ X5 @ X6))
% 0.60/0.82          | ~ (r2_hidden @ X4 @ X6)
% 0.60/0.82          | ~ (r2_hidden @ X4 @ X5))),
% 0.60/0.82      inference('simplify', [status(thm)], ['18'])).
% 0.60/0.82  thf('20', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (r2_hidden @ sk_D_1 @ X0)
% 0.60/0.82          | (r2_hidden @ sk_D_1 @ (k3_xboole_0 @ X0 @ sk_C_1)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['17', '19'])).
% 0.60/0.82  thf('21', plain,
% 0.60/0.82      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.60/0.82        | (r2_hidden @ sk_D_1 @ 
% 0.60/0.82           (k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_C_1)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['16', '20'])).
% 0.60/0.82  thf('22', plain,
% 0.60/0.82      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.60/0.82      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.60/0.82  thf('23', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(t74_xboole_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 0.60/0.82          ( r1_xboole_0 @ A @ B ) ) ))).
% 0.60/0.82  thf('24', plain,
% 0.60/0.82      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.60/0.82         (~ (r1_xboole_0 @ X23 @ X24)
% 0.60/0.82          | (r1_xboole_0 @ X23 @ (k3_xboole_0 @ X24 @ X25)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t74_xboole_1])).
% 0.60/0.82  thf('25', plain,
% 0.60/0.82      (![X0 : $i]: (r1_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.82  thf('26', plain,
% 0.60/0.82      (![X10 : $i, X11 : $i]:
% 0.60/0.82         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 0.60/0.82          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.60/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.82  thf('27', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ sk_B @ X0)) = (k1_xboole_0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['25', '26'])).
% 0.60/0.82  thf('28', plain,
% 0.60/0.82      ((((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))
% 0.60/0.82        | (r2_hidden @ sk_D_1 @ k1_xboole_0))),
% 0.60/0.82      inference('demod', [status(thm)], ['21', '22', '27'])).
% 0.60/0.82  thf('29', plain, ((r1_xboole_0 @ sk_C_1 @ sk_B)),
% 0.60/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.82  thf(symmetry_r1_xboole_0, axiom,
% 0.60/0.82    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.60/0.82  thf('30', plain,
% 0.60/0.82      (![X13 : $i, X14 : $i]:
% 0.60/0.82         ((r1_xboole_0 @ X13 @ X14) | ~ (r1_xboole_0 @ X14 @ X13))),
% 0.60/0.82      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.60/0.82  thf('31', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.60/0.82      inference('sup-', [status(thm)], ['29', '30'])).
% 0.60/0.82  thf('32', plain,
% 0.60/0.82      (![X10 : $i, X11 : $i]:
% 0.60/0.82         (((k3_xboole_0 @ X10 @ X11) = (k1_xboole_0))
% 0.60/0.82          | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.60/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.82  thf('33', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['31', '32'])).
% 0.60/0.82  thf(t4_xboole_0, axiom,
% 0.60/0.82    (![A:$i,B:$i]:
% 0.60/0.82     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.82            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.60/0.82       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.60/0.82            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.60/0.82  thf('34', plain,
% 0.60/0.82      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X17 @ (k3_xboole_0 @ X15 @ X18))
% 0.60/0.82          | ~ (r1_xboole_0 @ X15 @ X18))),
% 0.60/0.82      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.60/0.82  thf('35', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (~ (r2_hidden @ X0 @ k1_xboole_0) | ~ (r1_xboole_0 @ sk_B @ sk_C_1))),
% 0.60/0.82      inference('sup-', [status(thm)], ['33', '34'])).
% 0.60/0.82  thf('36', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.60/0.82      inference('sup-', [status(thm)], ['29', '30'])).
% 0.60/0.82  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.60/0.82      inference('demod', [status(thm)], ['35', '36'])).
% 0.60/0.82  thf('38', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_B @ sk_A))),
% 0.60/0.82      inference('clc', [status(thm)], ['28', '37'])).
% 0.60/0.82  thf('39', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.60/0.82      inference('sup-', [status(thm)], ['29', '30'])).
% 0.60/0.82  thf(t78_xboole_1, axiom,
% 0.60/0.82    (![A:$i,B:$i,C:$i]:
% 0.60/0.82     ( ( r1_xboole_0 @ A @ B ) =>
% 0.60/0.82       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 0.60/0.82         ( k3_xboole_0 @ A @ C ) ) ))).
% 0.60/0.82  thf('40', plain,
% 0.60/0.82      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.82         (~ (r1_xboole_0 @ X26 @ X27)
% 0.60/0.82          | ((k3_xboole_0 @ X26 @ (k2_xboole_0 @ X27 @ X28))
% 0.60/0.82              = (k3_xboole_0 @ X26 @ X28)))),
% 0.60/0.82      inference('cnf', [status(esa)], [t78_xboole_1])).
% 0.60/0.82  thf('41', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0))
% 0.60/0.82           = (k3_xboole_0 @ sk_B @ X0))),
% 0.60/0.82      inference('sup-', [status(thm)], ['39', '40'])).
% 0.60/0.82  thf('42', plain,
% 0.60/0.82      (![X10 : $i, X12 : $i]:
% 0.60/0.82         ((r1_xboole_0 @ X10 @ X12)
% 0.60/0.82          | ((k3_xboole_0 @ X10 @ X12) != (k1_xboole_0)))),
% 0.60/0.82      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.60/0.82  thf('43', plain,
% 0.60/0.82      (![X0 : $i]:
% 0.60/0.82         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 0.60/0.82          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ X0)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['41', '42'])).
% 0.60/0.82  thf('44', plain,
% 0.60/0.82      ((((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.82        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A)))),
% 0.60/0.82      inference('sup-', [status(thm)], ['38', '43'])).
% 0.60/0.82  thf('45', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_1 @ sk_A))),
% 0.60/0.82      inference('simplify', [status(thm)], ['44'])).
% 0.60/0.82  thf('46', plain,
% 0.60/0.82      (![X13 : $i, X14 : $i]:
% 0.60/0.82         ((r1_xboole_0 @ X13 @ X14) | ~ (r1_xboole_0 @ X14 @ X13))),
% 0.60/0.82      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.60/0.82  thf('47', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_A) @ sk_B)),
% 0.60/0.82      inference('sup-', [status(thm)], ['45', '46'])).
% 0.60/0.82  thf('48', plain, ($false), inference('demod', [status(thm)], ['2', '47'])).
% 0.60/0.82  
% 0.60/0.82  % SZS output end Refutation
% 0.60/0.82  
% 0.60/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
