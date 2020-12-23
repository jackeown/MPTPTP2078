%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.comvqbT5My

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:22 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.27s
% Verified   : 
% Statistics : Number of formulae       :   72 (  86 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :   14
%              Number of atoms          :  454 ( 644 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('4',plain,(
    ! [X29: $i] :
      ( ( k2_tarski @ X29 @ X29 )
      = ( k1_tarski @ X29 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t57_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r2_hidden @ A @ B )
        & ~ ( r2_hidden @ C @ B )
        & ~ ( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X35 @ X36 )
      | ( r1_xboole_0 @ ( k2_tarski @ X35 @ X37 ) @ X36 )
      | ( r2_hidden @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t57_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t74_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ( r1_xboole_0 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t74_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k1_tarski @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('12',plain,(
    r1_tarski @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference(demod,[status(thm)],['10','11'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k3_xboole_0 @ X19 @ X20 )
        = X19 )
      | ~ ( r1_tarski @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ ( k1_tarski @ sk_D ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('16',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) )
    = ( k3_xboole_0 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X13: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k3_xboole_0 @ X13 @ X16 ) )
      | ~ ( r1_xboole_0 @ X13 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_D ) @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_D @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','18'])).

thf('20',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ~ ( r2_hidden @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k3_xboole_0 @ sk_B @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','24'])).

thf('26',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['3','25'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('28',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('33',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_2 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_xboole_0 @ X4 @ X6 )
      | ( ( k3_xboole_0 @ X4 @ X6 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ sk_B @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_xboole_0 @ sk_B @ sk_C_2 ),
    inference(simplify,[status(thm)],['35'])).

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
    inference('sup-',[status(thm)],['28','40'])).

thf('42',plain,(
    r1_xboole_0 @ sk_B @ ( k2_xboole_0 @ sk_C_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['41'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.comvqbT5My
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.27/1.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.27/1.46  % Solved by: fo/fo7.sh
% 1.27/1.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.27/1.46  % done 1863 iterations in 1.013s
% 1.27/1.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.27/1.46  % SZS output start Refutation
% 1.27/1.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.27/1.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.27/1.46  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.27/1.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.27/1.46  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.27/1.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.27/1.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.27/1.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.27/1.46  thf(sk_D_type, type, sk_D: $i).
% 1.27/1.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.27/1.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.27/1.46  thf(sk_A_type, type, sk_A: $i).
% 1.27/1.46  thf(sk_B_type, type, sk_B: $i).
% 1.27/1.46  thf(t149_zfmisc_1, conjecture,
% 1.27/1.46    (![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.46     ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.27/1.46         ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.27/1.46       ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.27/1.46  thf(zf_stmt_0, negated_conjecture,
% 1.27/1.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 1.27/1.46        ( ( ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ ( k1_tarski @ D ) ) & 
% 1.27/1.46            ( r2_hidden @ D @ C ) & ( r1_xboole_0 @ C @ B ) ) =>
% 1.27/1.46          ( r1_xboole_0 @ ( k2_xboole_0 @ A @ C ) @ B ) ) )),
% 1.27/1.46    inference('cnf.neg', [status(esa)], [t149_zfmisc_1])).
% 1.27/1.46  thf('0', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_C_2) @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf(commutativity_k2_xboole_0, axiom,
% 1.27/1.46    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 1.27/1.46  thf('1', plain,
% 1.27/1.46      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.27/1.46      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 1.27/1.46  thf('2', plain, (~ (r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 1.27/1.46      inference('demod', [status(thm)], ['0', '1'])).
% 1.27/1.46  thf(t4_xboole_0, axiom,
% 1.27/1.46    (![A:$i,B:$i]:
% 1.27/1.46     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.27/1.46            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.27/1.46       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.27/1.46            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.27/1.46  thf('3', plain,
% 1.27/1.46      (![X13 : $i, X14 : $i]:
% 1.27/1.46         ((r1_xboole_0 @ X13 @ X14)
% 1.27/1.46          | (r2_hidden @ (sk_C_1 @ X14 @ X13) @ (k3_xboole_0 @ X13 @ X14)))),
% 1.27/1.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.27/1.46  thf(t69_enumset1, axiom,
% 1.27/1.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.27/1.46  thf('4', plain, (![X29 : $i]: ((k2_tarski @ X29 @ X29) = (k1_tarski @ X29))),
% 1.27/1.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.27/1.46  thf(t57_zfmisc_1, axiom,
% 1.27/1.46    (![A:$i,B:$i,C:$i]:
% 1.27/1.46     ( ~( ( ~( r2_hidden @ A @ B ) ) & ( ~( r2_hidden @ C @ B ) ) & 
% 1.27/1.46          ( ~( r1_xboole_0 @ ( k2_tarski @ A @ C ) @ B ) ) ) ))).
% 1.27/1.46  thf('5', plain,
% 1.27/1.46      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.27/1.46         ((r2_hidden @ X35 @ X36)
% 1.27/1.46          | (r1_xboole_0 @ (k2_tarski @ X35 @ X37) @ X36)
% 1.27/1.46          | (r2_hidden @ X37 @ X36))),
% 1.27/1.46      inference('cnf', [status(esa)], [t57_zfmisc_1])).
% 1.27/1.46  thf('6', plain,
% 1.27/1.46      (![X0 : $i, X1 : $i]:
% 1.27/1.46         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1)
% 1.27/1.46          | (r2_hidden @ X0 @ X1)
% 1.27/1.46          | (r2_hidden @ X0 @ X1))),
% 1.27/1.46      inference('sup+', [status(thm)], ['4', '5'])).
% 1.27/1.46  thf('7', plain,
% 1.27/1.46      (![X0 : $i, X1 : $i]:
% 1.27/1.46         ((r2_hidden @ X0 @ X1) | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 1.27/1.46      inference('simplify', [status(thm)], ['6'])).
% 1.27/1.46  thf(t74_xboole_1, axiom,
% 1.27/1.46    (![A:$i,B:$i,C:$i]:
% 1.27/1.46     ( ~( ( ~( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) & 
% 1.27/1.46          ( r1_xboole_0 @ A @ B ) ) ))).
% 1.27/1.46  thf('8', plain,
% 1.27/1.46      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.27/1.46         (~ (r1_xboole_0 @ X21 @ X22)
% 1.27/1.46          | (r1_xboole_0 @ X21 @ (k3_xboole_0 @ X22 @ X23)))),
% 1.27/1.46      inference('cnf', [status(esa)], [t74_xboole_1])).
% 1.27/1.46  thf('9', plain,
% 1.27/1.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.27/1.46         ((r2_hidden @ X1 @ X0)
% 1.27/1.46          | (r1_xboole_0 @ (k1_tarski @ X1) @ (k3_xboole_0 @ X0 @ X2)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['7', '8'])).
% 1.27/1.46  thf('10', plain,
% 1.27/1.46      ((r1_tarski @ (k3_xboole_0 @ sk_A @ sk_B) @ (k1_tarski @ sk_D))),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf(commutativity_k3_xboole_0, axiom,
% 1.27/1.46    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.27/1.46  thf('11', plain,
% 1.27/1.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.27/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.46  thf('12', plain,
% 1.27/1.46      ((r1_tarski @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))),
% 1.27/1.46      inference('demod', [status(thm)], ['10', '11'])).
% 1.27/1.46  thf(t28_xboole_1, axiom,
% 1.27/1.46    (![A:$i,B:$i]:
% 1.27/1.46     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.27/1.46  thf('13', plain,
% 1.27/1.46      (![X19 : $i, X20 : $i]:
% 1.27/1.46         (((k3_xboole_0 @ X19 @ X20) = (X19)) | ~ (r1_tarski @ X19 @ X20))),
% 1.27/1.46      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.27/1.46  thf('14', plain,
% 1.27/1.46      (((k3_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ (k1_tarski @ sk_D))
% 1.27/1.46         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.27/1.46      inference('sup-', [status(thm)], ['12', '13'])).
% 1.27/1.46  thf('15', plain,
% 1.27/1.46      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.27/1.46      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.46  thf('16', plain,
% 1.27/1.46      (((k3_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.27/1.46         = (k3_xboole_0 @ sk_B @ sk_A))),
% 1.27/1.46      inference('demod', [status(thm)], ['14', '15'])).
% 1.27/1.46  thf('17', plain,
% 1.27/1.46      (![X13 : $i, X15 : $i, X16 : $i]:
% 1.27/1.46         (~ (r2_hidden @ X15 @ (k3_xboole_0 @ X13 @ X16))
% 1.27/1.46          | ~ (r1_xboole_0 @ X13 @ X16))),
% 1.27/1.46      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.27/1.46  thf('18', plain,
% 1.27/1.46      (![X0 : $i]:
% 1.27/1.46         (~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))
% 1.27/1.46          | ~ (r1_xboole_0 @ (k1_tarski @ sk_D) @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['16', '17'])).
% 1.27/1.46  thf('19', plain,
% 1.27/1.46      (![X0 : $i]:
% 1.27/1.46         ((r2_hidden @ sk_D @ sk_B)
% 1.27/1.46          | ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A)))),
% 1.27/1.46      inference('sup-', [status(thm)], ['9', '18'])).
% 1.27/1.46  thf('20', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf('21', plain, ((r2_hidden @ sk_D @ sk_C_2)),
% 1.27/1.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.46  thf(t3_xboole_0, axiom,
% 1.27/1.46    (![A:$i,B:$i]:
% 1.27/1.46     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.27/1.46            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.27/1.46       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.27/1.46            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.27/1.46  thf('22', plain,
% 1.27/1.46      (![X9 : $i, X11 : $i, X12 : $i]:
% 1.27/1.46         (~ (r2_hidden @ X11 @ X9)
% 1.27/1.46          | ~ (r2_hidden @ X11 @ X12)
% 1.27/1.46          | ~ (r1_xboole_0 @ X9 @ X12))),
% 1.27/1.46      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.27/1.46  thf('23', plain,
% 1.27/1.46      (![X0 : $i]: (~ (r1_xboole_0 @ sk_C_2 @ X0) | ~ (r2_hidden @ sk_D @ X0))),
% 1.27/1.46      inference('sup-', [status(thm)], ['21', '22'])).
% 1.27/1.46  thf('24', plain, (~ (r2_hidden @ sk_D @ sk_B)),
% 1.27/1.46      inference('sup-', [status(thm)], ['20', '23'])).
% 1.27/1.46  thf('25', plain,
% 1.27/1.46      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k3_xboole_0 @ sk_B @ sk_A))),
% 1.27/1.46      inference('clc', [status(thm)], ['19', '24'])).
% 1.27/1.46  thf('26', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 1.27/1.46      inference('sup-', [status(thm)], ['3', '25'])).
% 1.27/1.47  thf(d7_xboole_0, axiom,
% 1.27/1.47    (![A:$i,B:$i]:
% 1.27/1.47     ( ( r1_xboole_0 @ A @ B ) <=>
% 1.27/1.47       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 1.27/1.47  thf('27', plain,
% 1.27/1.47      (![X4 : $i, X5 : $i]:
% 1.27/1.47         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.27/1.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.27/1.47  thf('28', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (k1_xboole_0))),
% 1.27/1.47      inference('sup-', [status(thm)], ['26', '27'])).
% 1.27/1.47  thf('29', plain, ((r1_xboole_0 @ sk_C_2 @ sk_B)),
% 1.27/1.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.27/1.47  thf('30', plain,
% 1.27/1.47      (![X4 : $i, X5 : $i]:
% 1.27/1.47         (((k3_xboole_0 @ X4 @ X5) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X4 @ X5))),
% 1.27/1.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.27/1.47  thf('31', plain, (((k3_xboole_0 @ sk_C_2 @ sk_B) = (k1_xboole_0))),
% 1.27/1.47      inference('sup-', [status(thm)], ['29', '30'])).
% 1.27/1.47  thf('32', plain,
% 1.27/1.47      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 1.27/1.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.27/1.47  thf('33', plain, (((k3_xboole_0 @ sk_B @ sk_C_2) = (k1_xboole_0))),
% 1.27/1.47      inference('demod', [status(thm)], ['31', '32'])).
% 1.27/1.47  thf('34', plain,
% 1.27/1.47      (![X4 : $i, X6 : $i]:
% 1.27/1.47         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.27/1.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.27/1.47  thf('35', plain,
% 1.27/1.47      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ sk_B @ sk_C_2))),
% 1.27/1.47      inference('sup-', [status(thm)], ['33', '34'])).
% 1.27/1.47  thf('36', plain, ((r1_xboole_0 @ sk_B @ sk_C_2)),
% 1.27/1.47      inference('simplify', [status(thm)], ['35'])).
% 1.27/1.47  thf(t78_xboole_1, axiom,
% 1.27/1.47    (![A:$i,B:$i,C:$i]:
% 1.27/1.47     ( ( r1_xboole_0 @ A @ B ) =>
% 1.27/1.47       ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) =
% 1.27/1.47         ( k3_xboole_0 @ A @ C ) ) ))).
% 1.27/1.47  thf('37', plain,
% 1.27/1.47      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.27/1.47         (~ (r1_xboole_0 @ X24 @ X25)
% 1.27/1.47          | ((k3_xboole_0 @ X24 @ (k2_xboole_0 @ X25 @ X26))
% 1.27/1.47              = (k3_xboole_0 @ X24 @ X26)))),
% 1.27/1.47      inference('cnf', [status(esa)], [t78_xboole_1])).
% 1.27/1.47  thf('38', plain,
% 1.27/1.47      (![X0 : $i]:
% 1.27/1.47         ((k3_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ X0))
% 1.27/1.47           = (k3_xboole_0 @ sk_B @ X0))),
% 1.27/1.47      inference('sup-', [status(thm)], ['36', '37'])).
% 1.27/1.47  thf('39', plain,
% 1.27/1.47      (![X4 : $i, X6 : $i]:
% 1.27/1.47         ((r1_xboole_0 @ X4 @ X6) | ((k3_xboole_0 @ X4 @ X6) != (k1_xboole_0)))),
% 1.27/1.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 1.27/1.47  thf('40', plain,
% 1.27/1.47      (![X0 : $i]:
% 1.27/1.47         (((k3_xboole_0 @ sk_B @ X0) != (k1_xboole_0))
% 1.27/1.47          | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ X0)))),
% 1.27/1.47      inference('sup-', [status(thm)], ['38', '39'])).
% 1.27/1.47  thf('41', plain,
% 1.27/1.47      ((((k1_xboole_0) != (k1_xboole_0))
% 1.27/1.47        | (r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ sk_A)))),
% 1.27/1.47      inference('sup-', [status(thm)], ['28', '40'])).
% 1.27/1.47  thf('42', plain, ((r1_xboole_0 @ sk_B @ (k2_xboole_0 @ sk_C_2 @ sk_A))),
% 1.27/1.47      inference('simplify', [status(thm)], ['41'])).
% 1.27/1.47  thf(symmetry_r1_xboole_0, axiom,
% 1.27/1.47    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 1.27/1.47  thf('43', plain,
% 1.27/1.47      (![X7 : $i, X8 : $i]:
% 1.27/1.47         ((r1_xboole_0 @ X7 @ X8) | ~ (r1_xboole_0 @ X8 @ X7))),
% 1.27/1.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 1.27/1.47  thf('44', plain, ((r1_xboole_0 @ (k2_xboole_0 @ sk_C_2 @ sk_A) @ sk_B)),
% 1.27/1.47      inference('sup-', [status(thm)], ['42', '43'])).
% 1.27/1.47  thf('45', plain, ($false), inference('demod', [status(thm)], ['2', '44'])).
% 1.27/1.47  
% 1.27/1.47  % SZS output end Refutation
% 1.27/1.47  
% 1.30/1.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
