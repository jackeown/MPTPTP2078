%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NezrFuinQe

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:25 EST 2020

% Result     : Theorem 2.52s
% Output     : Refutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 102 expanded)
%              Number of leaves         :   16 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :  429 ( 769 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ( r1_tarski @ A @ C )
          & ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('3',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r1_tarski @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X2 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_A ) @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('14',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X9 @ X11 )
      | ( r1_tarski @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X3 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ sk_C ) @ X0 )
      | ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ sk_A ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_A ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X7 @ X8 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X12 @ X13 ) @ ( k3_xboole_0 @ X12 @ X14 ) ) @ ( k2_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X3 @ ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) @ ( k3_xboole_0 @ X3 @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k3_xboole_0 @ X0 @ X2 ) )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_xboole_0 @ X16 @ X17 )
      | ( r1_xboole_0 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_B @ sk_A ) @ sk_A ),
    inference('sup-',[status(thm)],['21','38'])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ A @ B )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i] :
      ( ( r1_xboole_0 @ X18 @ X19 )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X18 @ X19 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('41',plain,(
    r1_xboole_0 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('43',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NezrFuinQe
% 0.16/0.36  % Computer   : n022.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 11:52:41 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 2.52/2.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.52/2.68  % Solved by: fo/fo7.sh
% 2.52/2.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.52/2.68  % done 3710 iterations in 2.201s
% 2.52/2.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.52/2.68  % SZS output start Refutation
% 2.52/2.68  thf(sk_B_type, type, sk_B: $i).
% 2.52/2.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.52/2.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.52/2.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.52/2.68  thf(sk_A_type, type, sk_A: $i).
% 2.52/2.68  thf(sk_C_type, type, sk_C: $i).
% 2.52/2.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.52/2.68  thf(t77_xboole_1, conjecture,
% 2.52/2.68    (![A:$i,B:$i,C:$i]:
% 2.52/2.68     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 2.52/2.68          ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ))).
% 2.52/2.68  thf(zf_stmt_0, negated_conjecture,
% 2.52/2.68    (~( ![A:$i,B:$i,C:$i]:
% 2.52/2.68        ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & ( r1_tarski @ A @ C ) & 
% 2.52/2.68             ( r1_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) ) )),
% 2.52/2.68    inference('cnf.neg', [status(esa)], [t77_xboole_1])).
% 2.52/2.68  thf('0', plain, (~ (r1_xboole_0 @ sk_A @ sk_B)),
% 2.52/2.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.68  thf('1', plain, ((r1_xboole_0 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C))),
% 2.52/2.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.68  thf(symmetry_r1_xboole_0, axiom,
% 2.52/2.68    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 2.52/2.68  thf('2', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i]:
% 2.52/2.68         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.52/2.68      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.52/2.68  thf('3', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_C) @ sk_A)),
% 2.52/2.68      inference('sup-', [status(thm)], ['1', '2'])).
% 2.52/2.68  thf('4', plain, ((r1_tarski @ sk_A @ sk_C)),
% 2.52/2.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.52/2.68  thf(t12_xboole_1, axiom,
% 2.52/2.68    (![A:$i,B:$i]:
% 2.52/2.68     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 2.52/2.68  thf('5', plain,
% 2.52/2.68      (![X5 : $i, X6 : $i]:
% 2.52/2.68         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 2.52/2.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.52/2.68  thf('6', plain, (((k2_xboole_0 @ sk_A @ sk_C) = (sk_C))),
% 2.52/2.68      inference('sup-', [status(thm)], ['4', '5'])).
% 2.52/2.68  thf(t31_xboole_1, axiom,
% 2.52/2.68    (![A:$i,B:$i,C:$i]:
% 2.52/2.68     ( r1_tarski @
% 2.52/2.68       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 2.52/2.68       ( k2_xboole_0 @ B @ C ) ))).
% 2.52/2.68  thf('7', plain,
% 2.52/2.68      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.52/2.68         (r1_tarski @ 
% 2.52/2.68          (k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k3_xboole_0 @ X12 @ X14)) @ 
% 2.52/2.68          (k2_xboole_0 @ X13 @ X14))),
% 2.52/2.68      inference('cnf', [status(esa)], [t31_xboole_1])).
% 2.52/2.68  thf(t11_xboole_1, axiom,
% 2.52/2.68    (![A:$i,B:$i,C:$i]:
% 2.52/2.68     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 2.52/2.68  thf('8', plain,
% 2.52/2.68      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.52/2.68         ((r1_tarski @ X2 @ X3) | ~ (r1_tarski @ (k2_xboole_0 @ X2 @ X4) @ X3))),
% 2.52/2.68      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.52/2.68  thf('9', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 2.52/2.68      inference('sup-', [status(thm)], ['7', '8'])).
% 2.52/2.68  thf('10', plain,
% 2.52/2.68      (![X0 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C)),
% 2.52/2.68      inference('sup+', [status(thm)], ['6', '9'])).
% 2.52/2.68  thf('11', plain,
% 2.52/2.68      (![X5 : $i, X6 : $i]:
% 2.52/2.68         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 2.52/2.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.52/2.68  thf('12', plain,
% 2.52/2.68      (![X0 : $i]: ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ sk_A) @ sk_C) = (sk_C))),
% 2.52/2.68      inference('sup-', [status(thm)], ['10', '11'])).
% 2.52/2.68  thf('13', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 2.52/2.68      inference('sup-', [status(thm)], ['7', '8'])).
% 2.52/2.68  thf(t17_xboole_1, axiom,
% 2.52/2.68    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.52/2.68  thf('14', plain,
% 2.52/2.68      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 2.52/2.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.52/2.68  thf(t19_xboole_1, axiom,
% 2.52/2.68    (![A:$i,B:$i,C:$i]:
% 2.52/2.68     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 2.52/2.68       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.52/2.68  thf('15', plain,
% 2.52/2.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.52/2.68         (~ (r1_tarski @ X9 @ X10)
% 2.52/2.68          | ~ (r1_tarski @ X9 @ X11)
% 2.52/2.68          | (r1_tarski @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 2.52/2.68      inference('cnf', [status(esa)], [t19_xboole_1])).
% 2.52/2.68  thf('16', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X2))
% 2.52/2.68          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 2.52/2.68      inference('sup-', [status(thm)], ['14', '15'])).
% 2.52/2.68  thf('17', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ 
% 2.52/2.68          (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 2.52/2.68      inference('sup-', [status(thm)], ['13', '16'])).
% 2.52/2.68  thf(t63_xboole_1, axiom,
% 2.52/2.68    (![A:$i,B:$i,C:$i]:
% 2.52/2.68     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 2.52/2.68       ( r1_xboole_0 @ A @ C ) ))).
% 2.52/2.68  thf('18', plain,
% 2.52/2.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.52/2.68         (~ (r1_tarski @ X15 @ X16)
% 2.52/2.68          | ~ (r1_xboole_0 @ X16 @ X17)
% 2.52/2.68          | (r1_xboole_0 @ X15 @ X17))),
% 2.52/2.68      inference('cnf', [status(esa)], [t63_xboole_1])).
% 2.52/2.68  thf('19', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.52/2.68         ((r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X3)
% 2.52/2.68          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X3))),
% 2.52/2.68      inference('sup-', [status(thm)], ['17', '18'])).
% 2.52/2.68  thf('20', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         (~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ sk_C) @ X0)
% 2.52/2.68          | (r1_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ sk_A)) @ X0))),
% 2.52/2.68      inference('sup-', [status(thm)], ['12', '19'])).
% 2.52/2.68  thf('21', plain,
% 2.52/2.68      (![X0 : $i]:
% 2.52/2.68         (r1_xboole_0 @ (k3_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_A)) @ sk_A)),
% 2.52/2.68      inference('sup-', [status(thm)], ['3', '20'])).
% 2.52/2.68  thf('22', plain,
% 2.52/2.68      (![X7 : $i, X8 : $i]: (r1_tarski @ (k3_xboole_0 @ X7 @ X8) @ X7)),
% 2.52/2.68      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.52/2.68  thf('23', plain,
% 2.52/2.68      (![X5 : $i, X6 : $i]:
% 2.52/2.68         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 2.52/2.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.52/2.68  thf('24', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i]:
% 2.52/2.68         ((k2_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 2.52/2.68      inference('sup-', [status(thm)], ['22', '23'])).
% 2.52/2.68  thf('25', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 2.52/2.68      inference('sup-', [status(thm)], ['7', '8'])).
% 2.52/2.68  thf('26', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         (r1_tarski @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0)),
% 2.52/2.68      inference('sup+', [status(thm)], ['24', '25'])).
% 2.52/2.68  thf('27', plain,
% 2.52/2.68      (![X5 : $i, X6 : $i]:
% 2.52/2.68         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 2.52/2.68      inference('cnf', [status(esa)], [t12_xboole_1])).
% 2.52/2.68  thf('28', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 2.52/2.68           = (X0))),
% 2.52/2.68      inference('sup-', [status(thm)], ['26', '27'])).
% 2.52/2.68  thf('29', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         ((k2_xboole_0 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ X0)
% 2.52/2.68           = (X0))),
% 2.52/2.68      inference('sup-', [status(thm)], ['26', '27'])).
% 2.52/2.68  thf('30', plain,
% 2.52/2.68      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.52/2.68         (r1_tarski @ 
% 2.52/2.68          (k2_xboole_0 @ (k3_xboole_0 @ X12 @ X13) @ (k3_xboole_0 @ X12 @ X14)) @ 
% 2.52/2.68          (k2_xboole_0 @ X13 @ X14))),
% 2.52/2.68      inference('cnf', [status(esa)], [t31_xboole_1])).
% 2.52/2.68  thf('31', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 2.52/2.68         (r1_tarski @ 
% 2.52/2.68          (k2_xboole_0 @ 
% 2.52/2.68           (k3_xboole_0 @ X3 @ (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X0 @ X1))) @ 
% 2.52/2.68           (k3_xboole_0 @ X3 @ X0)) @ 
% 2.52/2.68          X0)),
% 2.52/2.68      inference('sup+', [status(thm)], ['29', '30'])).
% 2.52/2.68  thf('32', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.52/2.68      inference('sup+', [status(thm)], ['28', '31'])).
% 2.52/2.68  thf('33', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X2))
% 2.52/2.68          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 2.52/2.68      inference('sup-', [status(thm)], ['14', '15'])).
% 2.52/2.68  thf('34', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i]:
% 2.52/2.68         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))),
% 2.52/2.68      inference('sup-', [status(thm)], ['32', '33'])).
% 2.52/2.68  thf('35', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         ((r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ (k3_xboole_0 @ X0 @ X2))
% 2.52/2.68          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2))),
% 2.52/2.68      inference('sup-', [status(thm)], ['14', '15'])).
% 2.52/2.68  thf('36', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i]:
% 2.52/2.68         (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ 
% 2.52/2.68          (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.52/2.68      inference('sup-', [status(thm)], ['34', '35'])).
% 2.52/2.68  thf('37', plain,
% 2.52/2.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.52/2.68         (~ (r1_tarski @ X15 @ X16)
% 2.52/2.68          | ~ (r1_xboole_0 @ X16 @ X17)
% 2.52/2.68          | (r1_xboole_0 @ X15 @ X17))),
% 2.52/2.68      inference('cnf', [status(esa)], [t63_xboole_1])).
% 2.52/2.68  thf('38', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.52/2.68         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 2.52/2.68          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X2))),
% 2.52/2.68      inference('sup-', [status(thm)], ['36', '37'])).
% 2.52/2.68  thf('39', plain, ((r1_xboole_0 @ (k3_xboole_0 @ sk_B @ sk_A) @ sk_A)),
% 2.52/2.68      inference('sup-', [status(thm)], ['21', '38'])).
% 2.52/2.68  thf(t75_xboole_1, axiom,
% 2.52/2.68    (![A:$i,B:$i]:
% 2.52/2.68     ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.52/2.68          ( r1_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ B ) ) ))).
% 2.52/2.68  thf('40', plain,
% 2.52/2.68      (![X18 : $i, X19 : $i]:
% 2.52/2.68         ((r1_xboole_0 @ X18 @ X19)
% 2.52/2.68          | ~ (r1_xboole_0 @ (k3_xboole_0 @ X18 @ X19) @ X19))),
% 2.52/2.68      inference('cnf', [status(esa)], [t75_xboole_1])).
% 2.52/2.68  thf('41', plain, ((r1_xboole_0 @ sk_B @ sk_A)),
% 2.52/2.68      inference('sup-', [status(thm)], ['39', '40'])).
% 2.52/2.68  thf('42', plain,
% 2.52/2.68      (![X0 : $i, X1 : $i]:
% 2.52/2.68         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 2.52/2.68      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 2.52/2.68  thf('43', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 2.52/2.68      inference('sup-', [status(thm)], ['41', '42'])).
% 2.52/2.68  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 2.52/2.68  
% 2.52/2.68  % SZS output end Refutation
% 2.52/2.68  
% 2.52/2.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
