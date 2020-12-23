%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o9h5zkCnCE

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 150 expanded)
%              Number of leaves         :   20 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  422 (1093 expanded)
%              Number of equality atoms :   34 (  88 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i,X19: $i] :
      ( ( X19
        = ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X19 @ X16 ) @ ( sk_D_1 @ X19 @ X16 ) ) @ X16 )
      | ( r2_hidden @ ( sk_C_1 @ X19 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t55_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_tarski @ X4 @ X5 ) @ X6 )
      | ~ ( r2_hidden @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t55_zfmisc_1])).

thf('5',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ o_0_0_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ o_0_0_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ o_0_0_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('8',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('9',plain,
    ( o_0_0_xboole_0
    = ( k1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ o_0_0_xboole_0 ) @ X0 )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k11_relat_1 @ X27 @ X28 ) )
      | ( r2_hidden @ ( k4_tarski @ X28 @ X26 ) @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C_1 @ ( k11_relat_1 @ X1 @ X0 ) @ o_0_0_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X16 )
      | ( r2_hidden @ X14 @ X17 )
      | ( X17
       != ( k1_relat_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('14',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k1_relat_1 @ X16 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = o_0_0_xboole_0 )
      | ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

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

thf('16',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['18'])).

thf('24',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X18 @ X17 )
      | ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_D_2 @ X18 @ X16 ) ) @ X16 )
      | ( X17
       != ( k1_relat_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('25',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_D_2 @ X18 @ X16 ) ) @ X16 )
      | ~ ( r2_hidden @ X18 @ ( k1_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_A @ ( sk_D_2 @ sk_A @ sk_B_1 ) ) @ sk_B_1 )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X28 @ X26 ) @ X27 )
      | ( r2_hidden @ X26 @ ( k11_relat_1 @ X27 @ X28 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('28',plain,
    ( ( ~ ( v1_relat_1 @ sk_B_1 )
      | ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_A ) )
   <= ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_A @ sk_B_1 ) @ o_0_0_xboole_0 )
   <= ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
      & ( ( k11_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) )
    | ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['16'])).

thf('35',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['19','33','34'])).

thf('36',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B_1 ) ) ),
    inference(simpl_trail,[status(thm)],['17','35'])).

thf('37',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
      = o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k11_relat_1 @ sk_B_1 @ sk_A )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['18'])).

thf('41',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('42',plain,
    ( ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != o_0_0_xboole_0 )
   <= ( ( k11_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['19','33'])).

thf('44',plain,(
    ( k11_relat_1 @ sk_B_1 @ sk_A )
 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['42','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.o9h5zkCnCE
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:32:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 127 iterations in 0.084s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.53  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.20/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.53  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.20/0.53  thf(d4_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.53       ( ![C:$i]:
% 0.20/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X16 : $i, X19 : $i]:
% 0.20/0.53         (((X19) = (k1_relat_1 @ X16))
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ (sk_C_1 @ X19 @ X16) @ (sk_D_1 @ X19 @ X16)) @ X16)
% 0.20/0.53          | (r2_hidden @ (sk_C_1 @ X19 @ X16) @ X19))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.53  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.53  thf('1', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.53      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.53  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.53  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.53  thf('3', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ o_0_0_xboole_0)),
% 0.20/0.53      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf(t55_zfmisc_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.53         (~ (r1_xboole_0 @ (k2_tarski @ X4 @ X5) @ X6)
% 0.20/0.53          | ~ (r2_hidden @ X4 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [t55_zfmisc_1])).
% 0.20/0.53  thf('5', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ o_0_0_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_1 @ X0 @ o_0_0_xboole_0) @ X0)
% 0.20/0.53          | ((X0) = (k1_relat_1 @ o_0_0_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_1 @ X0 @ o_0_0_xboole_0) @ X0)
% 0.20/0.53          | ((X0) = (k1_relat_1 @ o_0_0_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '5'])).
% 0.20/0.53  thf('8', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ o_0_0_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('9', plain, (((o_0_0_xboole_0) = (k1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_1 @ X0 @ o_0_0_xboole_0) @ X0)
% 0.20/0.53          | ((X0) = (o_0_0_xboole_0)))),
% 0.20/0.53      inference('demod', [status(thm)], ['6', '9'])).
% 0.20/0.53  thf(t204_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.53         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X26 @ (k11_relat_1 @ X27 @ X28))
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X28 @ X26) @ X27)
% 0.20/0.53          | ~ (v1_relat_1 @ X27))),
% 0.20/0.53      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (((k11_relat_1 @ X1 @ X0) = (o_0_0_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X1)
% 0.20/0.53          | (r2_hidden @ 
% 0.20/0.53             (k4_tarski @ X0 @ 
% 0.20/0.53              (sk_C_1 @ (k11_relat_1 @ X1 @ X0) @ o_0_0_xboole_0)) @ 
% 0.20/0.53             X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X16)
% 0.20/0.53          | (r2_hidden @ X14 @ X17)
% 0.20/0.53          | ((X17) != (k1_relat_1 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         ((r2_hidden @ X14 @ (k1_relat_1 @ X16))
% 0.20/0.53          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X16))),
% 0.20/0.53      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | ((k11_relat_1 @ X0 @ X1) = (o_0_0_xboole_0))
% 0.20/0.53          | (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '14'])).
% 0.20/0.53  thf(t205_relat_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.53         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i]:
% 0.20/0.53        ( ( v1_relat_1 @ B ) =>
% 0.20/0.53          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 0.20/0.53            ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t205_relat_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.20/0.53        | ~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      ((~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.20/0.53         <= (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['16'])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0))
% 0.20/0.53        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.53       ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('split', [status(esa)], ['18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.20/0.53         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['16'])).
% 0.20/0.53  thf('21', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (o_0_0_xboole_0)))
% 0.20/0.53         <= ((((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('split', [status(esa)], ['18'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X18 @ X17)
% 0.20/0.53          | (r2_hidden @ (k4_tarski @ X18 @ (sk_D_2 @ X18 @ X16)) @ X16)
% 0.20/0.53          | ((X17) != (k1_relat_1 @ X16)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X16 : $i, X18 : $i]:
% 0.20/0.53         ((r2_hidden @ (k4_tarski @ X18 @ (sk_D_2 @ X18 @ X16)) @ X16)
% 0.20/0.53          | ~ (r2_hidden @ X18 @ (k1_relat_1 @ X16)))),
% 0.20/0.53      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (((r2_hidden @ (k4_tarski @ sk_A @ (sk_D_2 @ sk_A @ sk_B_1)) @ sk_B_1))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '25'])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.53         (~ (r2_hidden @ (k4_tarski @ X28 @ X26) @ X27)
% 0.20/0.53          | (r2_hidden @ X26 @ (k11_relat_1 @ X27 @ X28))
% 0.20/0.53          | ~ (v1_relat_1 @ X27))),
% 0.20/0.53      inference('cnf', [status(esa)], [t204_relat_1])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((~ (v1_relat_1 @ sk_B_1)
% 0.20/0.53         | (r2_hidden @ (sk_D_2 @ sk_A @ sk_B_1) @ 
% 0.20/0.53            (k11_relat_1 @ sk_B_1 @ sk_A))))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.53  thf('29', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B_1) @ (k11_relat_1 @ sk_B_1 @ sk_A)))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.53      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (((r2_hidden @ (sk_D_2 @ sk_A @ sk_B_1) @ o_0_0_xboole_0))
% 0.20/0.53         <= (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) & 
% 0.20/0.53             (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('sup+', [status(thm)], ['22', '30'])).
% 0.20/0.53  thf('32', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ o_0_0_xboole_0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.20/0.53       ~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))) | 
% 0.20/0.53       (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('split', [status(esa)], ['16'])).
% 0.20/0.53  thf('35', plain, (~ ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['19', '33', '34'])).
% 0.20/0.53  thf('36', plain, (~ (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B_1))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['17', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) = (o_0_0_xboole_0))
% 0.20/0.53        | ~ (v1_relat_1 @ sk_B_1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '36'])).
% 0.20/0.53  thf('38', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('39', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) = (o_0_0_xboole_0))),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.20/0.53         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('split', [status(esa)], ['18'])).
% 0.20/0.53  thf('41', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.53      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((((k11_relat_1 @ sk_B_1 @ sk_A) != (o_0_0_xboole_0)))
% 0.20/0.53         <= (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.20/0.53      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain, (~ (((k11_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['19', '33'])).
% 0.20/0.53  thf('44', plain, (((k11_relat_1 @ sk_B_1 @ sk_A) != (o_0_0_xboole_0))),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['42', '43'])).
% 0.20/0.53  thf('45', plain, ($false),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['39', '44'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.37/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
