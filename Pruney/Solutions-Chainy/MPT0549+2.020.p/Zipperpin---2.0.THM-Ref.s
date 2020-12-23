%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M2q7Ajftnf

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 186 expanded)
%              Number of leaves         :   19 (  57 expanded)
%              Depth                    :   20
%              Number of atoms          :  531 (1442 expanded)
%              Number of equality atoms :   58 ( 140 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t151_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X3 @ X4 ) @ X4 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k7_relat_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['3','13'])).

thf(t149_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X9: $i] :
      ( ( ( k9_relat_1 @ X9 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t149_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X11 ) @ X12 )
      | ( ( k7_relat_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('25',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = k1_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('29',plain,
    ( ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = ( k9_relat_1 @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( v1_relat_1 @ X0 ) )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ~ ( v1_relat_1 @ X0 )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['14','35'])).

thf('37',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','36'])).

thf('38',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','37'])).

thf('39',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('40',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['22'])).

thf('41',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','36','40'])).

thf('42',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('44',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) )
        = ( k9_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('45',plain,(
    ! [X10: $i] :
      ( ( ( k2_relat_1 @ X10 )
       != k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k7_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k7_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ X11 @ X12 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('54',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['38','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M2q7Ajftnf
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 56 iterations in 0.022s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.48  thf(t151_relat_1, conjecture,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i,B:$i]:
% 0.20/0.48        ( ( v1_relat_1 @ B ) =>
% 0.20/0.48          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 0.20/0.48  thf('0', plain,
% 0.20/0.48      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.48        | ((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain,
% 0.20/0.48      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.48         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.20/0.48       ~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t4_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.48  thf(t79_xboole_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X3 @ X4) @ X4)),
% 0.20/0.48      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.20/0.48  thf('6', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.20/0.48  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.48  thf('8', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf(t95_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.48         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k1_relat_1 @ X11) @ X12)
% 0.20/0.48          | ((k7_relat_1 @ X11 @ X12) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.48  thf('10', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf(dt_k7_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         ((v1_relat_1 @ k1_xboole_0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.48  thf('14', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['3', '13'])).
% 0.20/0.48  thf(t149_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( k9_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X9 : $i]:
% 0.20/0.48         (((k9_relat_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X9))),
% 0.20/0.48      inference('cnf', [status(esa)], [t149_relat_1])).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf(t148_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.20/0.48          | ~ (v1_relat_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.48  thf('18', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0)
% 0.20/0.48          | ((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X0)
% 0.20/0.48          | ~ (v1_relat_1 @ X0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['15', '19'])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X0) | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.48        | ((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (~ (r1_xboole_0 @ (k1_relat_1 @ X11) @ X12)
% 0.20/0.48          | ((k7_relat_1 @ X11 @ X12) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (((~ (v1_relat_1 @ sk_B) | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))
% 0.20/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      ((((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.20/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.20/0.48          | ~ (v1_relat_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A))
% 0.20/0.48         | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup+', [status(thm)], ['27', '28'])).
% 0.20/0.48  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain,
% 0.20/0.48      ((((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ sk_B @ sk_A)))
% 0.20/0.48         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.48  thf('32', plain,
% 0.20/0.48      ((((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['0'])).
% 0.20/0.48  thf('33', plain,
% 0.20/0.48      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.20/0.48         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.48             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.48  thf('34', plain,
% 0.20/0.48      ((![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ X0)))
% 0.20/0.48         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.48             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '33'])).
% 0.20/0.48  thf('35', plain,
% 0.20/0.48      ((![X0 : $i]: ~ (v1_relat_1 @ X0))
% 0.20/0.48         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.48             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['34'])).
% 0.20/0.48  thf('36', plain,
% 0.20/0.48      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.48       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['14', '35'])).
% 0.20/0.48  thf('37', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '36'])).
% 0.20/0.48  thf('38', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['1', '37'])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.20/0.48         <= ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf('40', plain,
% 0.20/0.48      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.48       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('split', [status(esa)], ['22'])).
% 0.20/0.48  thf('41', plain, ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sat_resolution*', [status(thm)], ['2', '36', '40'])).
% 0.20/0.48  thf('42', plain, (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simpl_trail', [status(thm)], ['39', '41'])).
% 0.20/0.48  thf('43', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.48  thf('44', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k7_relat_1 @ X7 @ X8)) = (k9_relat_1 @ X7 @ X8))
% 0.20/0.48          | ~ (v1_relat_1 @ X7))),
% 0.20/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.48  thf(t64_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) =>
% 0.20/0.48       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.48           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.48         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.48  thf('45', plain,
% 0.20/0.48      (![X10 : $i]:
% 0.20/0.48         (((k2_relat_1 @ X10) != (k1_xboole_0))
% 0.20/0.48          | ((X10) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.48          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (v1_relat_1 @ X1)
% 0.20/0.48          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1)
% 0.20/0.48          | ((k9_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['43', '46'])).
% 0.20/0.48  thf('48', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (((k9_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 0.20/0.48          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.20/0.48          | ~ (v1_relat_1 @ X1))),
% 0.20/0.48      inference('simplify', [status(thm)], ['47'])).
% 0.20/0.48  thf('49', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.48        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['42', '48'])).
% 0.20/0.48  thf('50', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('51', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.48      inference('demod', [status(thm)], ['49', '50'])).
% 0.20/0.48  thf('52', plain, (((k7_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 0.20/0.48      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (![X11 : $i, X12 : $i]:
% 0.20/0.48         (((k7_relat_1 @ X11 @ X12) != (k1_xboole_0))
% 0.20/0.48          | (r1_xboole_0 @ (k1_relat_1 @ X11) @ X12)
% 0.20/0.48          | ~ (v1_relat_1 @ X11))),
% 0.20/0.48      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.48  thf('54', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.48        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['52', '53'])).
% 0.20/0.48  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('56', plain,
% 0.20/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.48        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.48  thf('57', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.48      inference('simplify', [status(thm)], ['56'])).
% 0.20/0.48  thf('58', plain, ($false), inference('demod', [status(thm)], ['38', '57'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
