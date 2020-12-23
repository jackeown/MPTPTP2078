%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oSBeUEjiLX

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:17 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 117 expanded)
%              Number of leaves         :   28 (  46 expanded)
%              Depth                    :   19
%              Number of atoms          :  431 ( 683 expanded)
%              Number of equality atoms :   45 (  67 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X23: $i] :
      ( ( X23
        = ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X23 @ X20 ) @ ( sk_D_1 @ X23 @ X20 ) ) @ X20 )
      | ( r2_hidden @ ( sk_C_1 @ X23 @ X20 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X15: $i] :
      ( ( k3_xboole_0 @ X15 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('6',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('9',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X28: $i] :
      ( ( ( k1_relat_1 @ X28 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('11',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X27 @ X26 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X27 ) @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k2_xboole_0 @ X6 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('16',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ( r2_hidden @ X3 @ ( k2_xboole_0 @ X6 @ X4 ) )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X0 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf(t60_relat_1,conjecture,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ( ( ( k1_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      & ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_relat_1])).

thf('22',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('24',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('25',plain,(
    ! [X13: $i] :
      ( ( X13 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X13 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['22'])).

thf('35',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['33','34'])).

thf('36',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['23','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','37'])).

thf('39',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','40'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X25: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oSBeUEjiLX
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:45:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.71  % Solved by: fo/fo7.sh
% 0.49/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.71  % done 554 iterations in 0.252s
% 0.49/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.71  % SZS output start Refutation
% 0.49/0.71  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.49/0.71  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.49/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.71  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.49/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.49/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.49/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.71  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.49/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.71  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.49/0.71  thf(cc1_relat_1, axiom,
% 0.49/0.71    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.49/0.71  thf('0', plain, (![X17 : $i]: ((v1_relat_1 @ X17) | ~ (v1_xboole_0 @ X17))),
% 0.49/0.71      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.49/0.71  thf(d4_relat_1, axiom,
% 0.49/0.71    (![A:$i,B:$i]:
% 0.49/0.71     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.49/0.71       ( ![C:$i]:
% 0.49/0.71         ( ( r2_hidden @ C @ B ) <=>
% 0.49/0.71           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.49/0.71  thf('1', plain,
% 0.49/0.71      (![X20 : $i, X23 : $i]:
% 0.49/0.71         (((X23) = (k1_relat_1 @ X20))
% 0.49/0.71          | (r2_hidden @ 
% 0.49/0.71             (k4_tarski @ (sk_C_1 @ X23 @ X20) @ (sk_D_1 @ X23 @ X20)) @ X20)
% 0.49/0.71          | (r2_hidden @ (sk_C_1 @ X23 @ X20) @ X23))),
% 0.49/0.71      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.49/0.71  thf(t2_boole, axiom,
% 0.49/0.71    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.71  thf('2', plain,
% 0.49/0.71      (![X15 : $i]: ((k3_xboole_0 @ X15 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.71      inference('cnf', [status(esa)], [t2_boole])).
% 0.49/0.71  thf(t4_xboole_0, axiom,
% 0.49/0.71    (![A:$i,B:$i]:
% 0.49/0.71     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.49/0.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.49/0.71            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.49/0.71  thf('3', plain,
% 0.49/0.71      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 0.49/0.71          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.49/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.49/0.71  thf('4', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.71  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.49/0.71  thf('5', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.49/0.71  thf('6', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.49/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.49/0.71  thf('7', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.49/0.71          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['1', '6'])).
% 0.49/0.71  thf('8', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.49/0.71      inference('demod', [status(thm)], ['4', '5'])).
% 0.49/0.71  thf('9', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.71  thf(t37_relat_1, axiom,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ( v1_relat_1 @ A ) =>
% 0.49/0.71       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.49/0.71         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.49/0.71  thf('10', plain,
% 0.49/0.71      (![X28 : $i]:
% 0.49/0.71         (((k1_relat_1 @ X28) = (k2_relat_1 @ (k4_relat_1 @ X28)))
% 0.49/0.71          | ~ (v1_relat_1 @ X28))),
% 0.49/0.71      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.49/0.71  thf('11', plain, (![X17 : $i]: ((v1_relat_1 @ X17) | ~ (v1_xboole_0 @ X17))),
% 0.49/0.71      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.49/0.71  thf(t1_boole, axiom,
% 0.49/0.71    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.49/0.71  thf('12', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.49/0.71      inference('cnf', [status(esa)], [t1_boole])).
% 0.49/0.71  thf(t26_relat_1, axiom,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ( v1_relat_1 @ A ) =>
% 0.49/0.71       ( ![B:$i]:
% 0.49/0.71         ( ( v1_relat_1 @ B ) =>
% 0.49/0.71           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 0.49/0.71             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.49/0.71  thf('13', plain,
% 0.49/0.71      (![X26 : $i, X27 : $i]:
% 0.49/0.71         (~ (v1_relat_1 @ X26)
% 0.49/0.71          | ((k2_relat_1 @ (k2_xboole_0 @ X27 @ X26))
% 0.49/0.71              = (k2_xboole_0 @ (k2_relat_1 @ X27) @ (k2_relat_1 @ X26)))
% 0.49/0.71          | ~ (v1_relat_1 @ X27))),
% 0.49/0.71      inference('cnf', [status(esa)], [t26_relat_1])).
% 0.49/0.71  thf(t7_xboole_0, axiom,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.49/0.71          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.49/0.71  thf('14', plain,
% 0.49/0.71      (![X13 : $i]:
% 0.49/0.71         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 0.49/0.71      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.49/0.71  thf(d3_xboole_0, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.49/0.71       ( ![D:$i]:
% 0.49/0.71         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.71           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.49/0.71  thf('15', plain,
% 0.49/0.71      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X3 @ X4)
% 0.49/0.71          | (r2_hidden @ X3 @ X5)
% 0.49/0.71          | ((X5) != (k2_xboole_0 @ X6 @ X4)))),
% 0.49/0.71      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.49/0.71  thf('16', plain,
% 0.49/0.71      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.49/0.71         ((r2_hidden @ X3 @ (k2_xboole_0 @ X6 @ X4)) | ~ (r2_hidden @ X3 @ X4))),
% 0.49/0.71      inference('simplify', [status(thm)], ['15'])).
% 0.49/0.71  thf('17', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (((X0) = (k1_xboole_0))
% 0.49/0.71          | (r2_hidden @ (sk_B_1 @ X0) @ (k2_xboole_0 @ X1 @ X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['14', '16'])).
% 0.49/0.71  thf(d1_xboole_0, axiom,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.49/0.71  thf('18', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.71  thf('19', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['17', '18'])).
% 0.49/0.71  thf('20', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]:
% 0.49/0.71         (~ (v1_xboole_0 @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.49/0.71          | ~ (v1_relat_1 @ X1)
% 0.49/0.71          | ~ (v1_relat_1 @ X0)
% 0.49/0.71          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['13', '19'])).
% 0.49/0.71  thf('21', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.49/0.71          | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.49/0.71          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.71          | ~ (v1_relat_1 @ X0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['12', '20'])).
% 0.49/0.71  thf(t60_relat_1, conjecture,
% 0.49/0.71    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.49/0.71     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.49/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.71    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.49/0.71        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.49/0.71    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.49/0.71  thf('22', plain,
% 0.49/0.71      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.49/0.71        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('23', plain,
% 0.49/0.71      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.49/0.71         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['22'])).
% 0.49/0.71  thf('24', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.71  thf('25', plain,
% 0.49/0.71      (![X13 : $i]:
% 0.49/0.71         (((X13) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X13) @ X13))),
% 0.49/0.71      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.49/0.71  thf('26', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.71  thf('27', plain,
% 0.49/0.71      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['25', '26'])).
% 0.49/0.71  thf('28', plain,
% 0.49/0.71      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.49/0.71         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.71      inference('split', [status(esa)], ['22'])).
% 0.49/0.71  thf('29', plain,
% 0.49/0.71      ((![X0 : $i]:
% 0.49/0.71          (((k1_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.49/0.71         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['27', '28'])).
% 0.49/0.71  thf('30', plain,
% 0.49/0.71      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.49/0.71         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['24', '29'])).
% 0.49/0.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.49/0.71  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.71  thf('32', plain,
% 0.49/0.71      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.49/0.71         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.49/0.71      inference('demod', [status(thm)], ['30', '31'])).
% 0.49/0.71  thf('33', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.49/0.71      inference('simplify', [status(thm)], ['32'])).
% 0.49/0.71  thf('34', plain,
% 0.49/0.71      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.49/0.71       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.49/0.71      inference('split', [status(esa)], ['22'])).
% 0.49/0.71  thf('35', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.49/0.71      inference('sat_resolution*', [status(thm)], ['33', '34'])).
% 0.49/0.71  thf('36', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.49/0.71      inference('simpl_trail', [status(thm)], ['23', '35'])).
% 0.49/0.71  thf('37', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.49/0.71          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.71          | ~ (v1_relat_1 @ X0))),
% 0.49/0.71      inference('simplify_reflect-', [status(thm)], ['21', '36'])).
% 0.49/0.71  thf('38', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.49/0.71          | ~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['11', '37'])).
% 0.49/0.71  thf('39', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.71  thf('40', plain,
% 0.49/0.71      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.49/0.71      inference('demod', [status(thm)], ['38', '39'])).
% 0.49/0.71  thf('41', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.49/0.71          | ~ (v1_relat_1 @ X0)
% 0.49/0.71          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['10', '40'])).
% 0.49/0.71  thf(dt_k4_relat_1, axiom,
% 0.49/0.71    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.49/0.71  thf('42', plain,
% 0.49/0.71      (![X25 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X25)) | ~ (v1_relat_1 @ X25))),
% 0.49/0.71      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.49/0.71  thf('43', plain,
% 0.49/0.71      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.49/0.71      inference('clc', [status(thm)], ['41', '42'])).
% 0.49/0.71  thf('44', plain,
% 0.49/0.71      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['9', '43'])).
% 0.49/0.71  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.71  thf('46', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.49/0.71      inference('demod', [status(thm)], ['44', '45'])).
% 0.49/0.71  thf('47', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.71      inference('sup-', [status(thm)], ['0', '46'])).
% 0.49/0.71  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.71  thf('49', plain, ($false), inference('demod', [status(thm)], ['47', '48'])).
% 0.49/0.71  
% 0.49/0.71  % SZS output end Refutation
% 0.49/0.71  
% 0.49/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
