%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G3sEdSV6Gc

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:43 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 134 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :   14
%              Number of atoms          :  462 (1074 expanded)
%              Number of equality atoms :   39 (  90 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14
        = ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X14 @ X11 ) @ ( sk_D @ X14 @ X11 ) ) @ X11 )
      | ( r2_hidden @ ( sk_C @ X14 @ X11 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( r1_xboole_0 @ X2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('3',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf('6',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('7',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','7'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k11_relat_1 @ X19 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ X20 @ X18 ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C @ ( k11_relat_1 @ X1 @ X0 ) @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 )
      | ( r2_hidden @ X9 @ X12 )
      | ( X12
       != ( k1_relat_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X9 @ X10 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t205_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
        <=> ( ( k11_relat_1 @ B @ A )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t205_relat_1])).

thf('14',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['16'])).

thf('19',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k11_relat_1 @ X7 @ X8 )
        = ( k9_relat_1 @ X7 @ ( k1_tarski @ X8 ) ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k9_relat_1 @ X16 @ X17 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('29',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
    ! [X3: $i] :
      ( ( k2_tarski @ X3 @ X3 )
      = ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['14'])).

thf('36',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sat_resolution*',[status(thm)],['17','34','35'])).

thf('37',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simpl_trail,[status(thm)],['15','36'])).

thf('38',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('42',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['17','34'])).

thf('43',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.G3sEdSV6Gc
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:21:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 55 iterations in 0.034s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.35/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.35/0.53  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.35/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.35/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.35/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.35/0.53  thf(d4_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.35/0.53       ( ![C:$i]:
% 0.35/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.35/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      (![X11 : $i, X14 : $i]:
% 0.35/0.53         (((X14) = (k1_relat_1 @ X11))
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (k4_tarski @ (sk_C @ X14 @ X11) @ (sk_D @ X14 @ X11)) @ X11)
% 0.35/0.53          | (r2_hidden @ (sk_C @ X14 @ X11) @ X14))),
% 0.35/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.35/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.35/0.53  thf('1', plain, (![X2 : $i]: (r1_xboole_0 @ X2 @ k1_xboole_0)),
% 0.35/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.35/0.53  thf(t55_zfmisc_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.53         (~ (r1_xboole_0 @ (k2_tarski @ X4 @ X5) @ X6)
% 0.35/0.53          | ~ (r2_hidden @ X4 @ X6))),
% 0.35/0.53      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.35/0.53  thf('3', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.35/0.53          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.35/0.53          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['0', '3'])).
% 0.35/0.53  thf('6', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.35/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.35/0.53  thf('7', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.35/0.53      inference('sup-', [status(thm)], ['5', '6'])).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X0 : $i]:
% 0.35/0.53         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.35/0.53      inference('demod', [status(thm)], ['4', '7'])).
% 0.35/0.53  thf(t204_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ C ) =>
% 0.35/0.53       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.35/0.53         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X18 @ (k11_relat_1 @ X19 @ X20))
% 0.35/0.53          | (r2_hidden @ (k4_tarski @ X20 @ X18) @ X19)
% 0.35/0.53          | ~ (v1_relat_1 @ X19))),
% 0.35/0.53      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.35/0.53          | ~ (v1_relat_1 @ X1)
% 0.35/0.53          | (r2_hidden @ 
% 0.35/0.53             (k4_tarski @ X0 @ (sk_C @ (k11_relat_1 @ X1 @ X0) @ k1_xboole_0)) @ 
% 0.35/0.53             X1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['8', '9'])).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.53         (~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11)
% 0.35/0.53          | (r2_hidden @ X9 @ X12)
% 0.35/0.53          | ((X12) != (k1_relat_1 @ X11)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.35/0.53  thf('12', plain,
% 0.35/0.53      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.53         ((r2_hidden @ X9 @ (k1_relat_1 @ X11))
% 0.35/0.53          | ~ (r2_hidden @ (k4_tarski @ X9 @ X10) @ X11))),
% 0.35/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (v1_relat_1 @ X0)
% 0.35/0.53          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.35/0.53          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['10', '12'])).
% 0.35/0.53  thf(t205_relat_1, conjecture,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ B ) =>
% 0.35/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.35/0.53         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i]:
% 0.35/0.53        ( ( v1_relat_1 @ B ) =>
% 0.35/0.53          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.35/0.53            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 0.35/0.53        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.35/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['14'])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))
% 0.35/0.53        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.35/0.53       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['16'])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.35/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['16'])).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.35/0.53         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('split', [status(esa)], ['14'])).
% 0.35/0.53  thf(d16_relat_1, axiom,
% 0.35/0.53    (![A:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ A ) =>
% 0.35/0.53       ( ![B:$i]:
% 0.35/0.53         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X7 : $i, X8 : $i]:
% 0.35/0.53         (((k11_relat_1 @ X7 @ X8) = (k9_relat_1 @ X7 @ (k1_tarski @ X8)))
% 0.35/0.53          | ~ (v1_relat_1 @ X7))),
% 0.35/0.53      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.35/0.53  thf(t151_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( v1_relat_1 @ B ) =>
% 0.35/0.53       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.35/0.53         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      (![X16 : $i, X17 : $i]:
% 0.35/0.53         (((k9_relat_1 @ X16 @ X17) != (k1_xboole_0))
% 0.35/0.53          | (r1_xboole_0 @ (k1_relat_1 @ X16) @ X17)
% 0.35/0.53          | ~ (v1_relat_1 @ X16))),
% 0.35/0.53      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (((k11_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.35/0.53          | ~ (v1_relat_1 @ X1)
% 0.35/0.53          | ~ (v1_relat_1 @ X1)
% 0.35/0.53          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 0.35/0.53          | ~ (v1_relat_1 @ X1)
% 0.35/0.53          | ((k11_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['22'])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      (((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.53         | ~ (v1_relat_1 @ sk_B)
% 0.35/0.53         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.35/0.53         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['19', '23'])).
% 0.35/0.53  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (((((k1_xboole_0) != (k1_xboole_0))
% 0.35/0.53         | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.35/0.53         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('demod', [status(thm)], ['24', '25'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.35/0.53         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('simplify', [status(thm)], ['26'])).
% 0.35/0.53  thf(symmetry_r1_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.35/0.53      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k1_relat_1 @ sk_B)))
% 0.35/0.53         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['27', '28'])).
% 0.35/0.53  thf(t69_enumset1, axiom,
% 0.35/0.53    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.35/0.53  thf('30', plain, (![X3 : $i]: ((k2_tarski @ X3 @ X3) = (k1_tarski @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.35/0.53         (~ (r1_xboole_0 @ (k2_tarski @ X4 @ X5) @ X6)
% 0.35/0.53          | ~ (r2_hidden @ X4 @ X6))),
% 0.35/0.53      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      (![X0 : $i, X1 : $i]:
% 0.35/0.53         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.35/0.53      inference('sup-', [status(thm)], ['30', '31'])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))
% 0.35/0.53         <= ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['29', '32'])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.35/0.53       ~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.35/0.53      inference('sup-', [status(thm)], ['18', '33'])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))) | 
% 0.35/0.53       (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.35/0.53      inference('split', [status(esa)], ['14'])).
% 0.35/0.53  thf('36', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.35/0.53      inference('sat_resolution*', [status(thm)], ['17', '34', '35'])).
% 0.35/0.53  thf('37', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.35/0.53      inference('simpl_trail', [status(thm)], ['15', '36'])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      ((((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['13', '37'])).
% 0.35/0.53  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('40', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.35/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      ((((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.35/0.53         <= (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.35/0.53      inference('split', [status(esa)], ['16'])).
% 0.35/0.53  thf('42', plain, (~ (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.35/0.54      inference('sat_resolution*', [status(thm)], ['17', '34'])).
% 0.35/0.54  thf('43', plain, (((k11_relat_1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.35/0.54      inference('simpl_trail', [status(thm)], ['41', '42'])).
% 0.35/0.54  thf('44', plain, ($false),
% 0.35/0.54      inference('simplify_reflect-', [status(thm)], ['40', '43'])).
% 0.35/0.54  
% 0.35/0.54  % SZS output end Refutation
% 0.35/0.54  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
