%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yYlRxmkeVJ

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:17 EST 2020

% Result     : Theorem 0.33s
% Output     : Refutation 0.33s
% Verified   : 
% Statistics : Number of formulae       :   77 (  92 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :   14
%              Number of atoms          :  444 ( 534 expanded)
%              Number of equality atoms :   36 (  49 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X19 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_D_1 @ X19 @ X17 ) ) @ X17 )
      | ( X18
       != ( k1_relat_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('3',plain,(
    ! [X17: $i,X19: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X19 @ ( sk_D_1 @ X19 @ X17 ) ) @ X17 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k2_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

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

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('20',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X11 @ X12 )
        = X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k4_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['7','22'])).

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

thf('24',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('26',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20
        = ( k1_relat_1 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X20 @ X17 ) @ ( sk_D @ X20 @ X17 ) ) @ X17 )
      | ( r2_hidden @ ( sk_C_1 @ X20 @ X17 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('simplify_reflect+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['24'])).

thf('39',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['25','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['23','40'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X22: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','43'])).

thf('45',plain,(
    ! [X14: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yYlRxmkeVJ
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.33/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.33/0.55  % Solved by: fo/fo7.sh
% 0.33/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.33/0.55  % done 133 iterations in 0.124s
% 0.33/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.33/0.55  % SZS output start Refutation
% 0.33/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.33/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.33/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.33/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.33/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.33/0.55  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.33/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.33/0.55  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.33/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.33/0.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.33/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.33/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.33/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.33/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.33/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.33/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.33/0.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.33/0.55  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.33/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.33/0.55  thf(d1_xboole_0, axiom,
% 0.33/0.55    (![A:$i]:
% 0.33/0.55     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.33/0.55  thf('1', plain,
% 0.33/0.55      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.33/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.33/0.55  thf(d4_relat_1, axiom,
% 0.33/0.55    (![A:$i,B:$i]:
% 0.33/0.55     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.33/0.55       ( ![C:$i]:
% 0.33/0.55         ( ( r2_hidden @ C @ B ) <=>
% 0.33/0.55           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.33/0.55  thf('2', plain,
% 0.33/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.33/0.55         (~ (r2_hidden @ X19 @ X18)
% 0.33/0.55          | (r2_hidden @ (k4_tarski @ X19 @ (sk_D_1 @ X19 @ X17)) @ X17)
% 0.33/0.55          | ((X18) != (k1_relat_1 @ X17)))),
% 0.33/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.33/0.55  thf('3', plain,
% 0.33/0.55      (![X17 : $i, X19 : $i]:
% 0.33/0.55         ((r2_hidden @ (k4_tarski @ X19 @ (sk_D_1 @ X19 @ X17)) @ X17)
% 0.33/0.55          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X17)))),
% 0.33/0.55      inference('simplify', [status(thm)], ['2'])).
% 0.33/0.55  thf('4', plain,
% 0.33/0.55      (![X0 : $i]:
% 0.33/0.55         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.33/0.55          | (r2_hidden @ 
% 0.33/0.55             (k4_tarski @ (sk_B @ (k1_relat_1 @ X0)) @ 
% 0.33/0.55              (sk_D_1 @ (sk_B @ (k1_relat_1 @ X0)) @ X0)) @ 
% 0.33/0.55             X0))),
% 0.33/0.55      inference('sup-', [status(thm)], ['1', '3'])).
% 0.33/0.55  thf('5', plain,
% 0.33/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.33/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.33/0.55  thf('6', plain,
% 0.33/0.55      (![X0 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.33/0.55      inference('sup-', [status(thm)], ['4', '5'])).
% 0.33/0.55  thf(t37_relat_1, axiom,
% 0.33/0.55    (![A:$i]:
% 0.33/0.55     ( ( v1_relat_1 @ A ) =>
% 0.33/0.55       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.33/0.55         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.33/0.55  thf('7', plain,
% 0.33/0.55      (![X25 : $i]:
% 0.33/0.55         (((k1_relat_1 @ X25) = (k2_relat_1 @ (k4_relat_1 @ X25)))
% 0.33/0.55          | ~ (v1_relat_1 @ X25))),
% 0.33/0.55      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.33/0.55  thf(cc1_relat_1, axiom,
% 0.33/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.33/0.55  thf('8', plain, (![X14 : $i]: ((v1_relat_1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.33/0.55      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.33/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.33/0.55  thf('9', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.33/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.33/0.55  thf(t25_relat_1, axiom,
% 0.33/0.55    (![A:$i]:
% 0.33/0.55     ( ( v1_relat_1 @ A ) =>
% 0.33/0.55       ( ![B:$i]:
% 0.33/0.55         ( ( v1_relat_1 @ B ) =>
% 0.33/0.55           ( ( r1_tarski @ A @ B ) =>
% 0.33/0.55             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.33/0.55               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.33/0.55  thf('10', plain,
% 0.33/0.55      (![X23 : $i, X24 : $i]:
% 0.33/0.55         (~ (v1_relat_1 @ X23)
% 0.33/0.55          | (r1_tarski @ (k2_relat_1 @ X24) @ (k2_relat_1 @ X23))
% 0.33/0.55          | ~ (r1_tarski @ X24 @ X23)
% 0.33/0.55          | ~ (v1_relat_1 @ X24))),
% 0.33/0.55      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.33/0.55  thf('11', plain,
% 0.33/0.55      (![X0 : $i]:
% 0.33/0.55         (~ (v1_relat_1 @ k1_xboole_0)
% 0.33/0.55          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ (k2_relat_1 @ X0))
% 0.33/0.55          | ~ (v1_relat_1 @ X0))),
% 0.33/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.33/0.55  thf('12', plain,
% 0.33/0.55      (![X0 : $i]:
% 0.33/0.55         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.33/0.55          | ~ (v1_relat_1 @ X0)
% 0.33/0.55          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ (k2_relat_1 @ X0)))),
% 0.33/0.55      inference('sup-', [status(thm)], ['8', '11'])).
% 0.33/0.55  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.33/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.33/0.55  thf('14', plain,
% 0.33/0.55      (![X0 : $i]:
% 0.33/0.55         (~ (v1_relat_1 @ X0)
% 0.33/0.55          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ (k2_relat_1 @ X0)))),
% 0.33/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.33/0.55  thf(l32_xboole_1, axiom,
% 0.33/0.55    (![A:$i,B:$i]:
% 0.33/0.55     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.33/0.55  thf('15', plain,
% 0.33/0.55      (![X7 : $i, X9 : $i]:
% 0.33/0.55         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.33/0.55      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.33/0.55  thf('16', plain,
% 0.33/0.55      (![X0 : $i]:
% 0.33/0.55         (~ (v1_relat_1 @ X0)
% 0.33/0.55          | ((k4_xboole_0 @ (k2_relat_1 @ k1_xboole_0) @ (k2_relat_1 @ X0))
% 0.33/0.55              = (k1_xboole_0)))),
% 0.33/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.33/0.55  thf(t3_xboole_0, axiom,
% 0.33/0.55    (![A:$i,B:$i]:
% 0.33/0.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.33/0.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.33/0.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.33/0.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.33/0.55  thf('17', plain,
% 0.33/0.55      (![X3 : $i, X4 : $i]:
% 0.33/0.55         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.33/0.55      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.33/0.55  thf('18', plain,
% 0.33/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.33/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.33/0.55  thf('19', plain,
% 0.33/0.55      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.33/0.55      inference('sup-', [status(thm)], ['17', '18'])).
% 0.33/0.55  thf(t83_xboole_1, axiom,
% 0.33/0.55    (![A:$i,B:$i]:
% 0.33/0.55     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.33/0.55  thf('20', plain,
% 0.33/0.55      (![X11 : $i, X12 : $i]:
% 0.33/0.55         (((k4_xboole_0 @ X11 @ X12) = (X11)) | ~ (r1_xboole_0 @ X11 @ X12))),
% 0.33/0.55      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.33/0.55  thf('21', plain,
% 0.33/0.55      (![X0 : $i, X1 : $i]:
% 0.33/0.55         (~ (v1_xboole_0 @ X0) | ((k4_xboole_0 @ X1 @ X0) = (X1)))),
% 0.33/0.55      inference('sup-', [status(thm)], ['19', '20'])).
% 0.33/0.55  thf('22', plain,
% 0.33/0.55      (![X0 : $i]:
% 0.33/0.55         (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.33/0.55          | ~ (v1_relat_1 @ X0)
% 0.33/0.55          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.33/0.55      inference('sup+', [status(thm)], ['16', '21'])).
% 0.33/0.55  thf('23', plain,
% 0.33/0.55      (![X0 : $i]:
% 0.33/0.55         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.33/0.55          | ~ (v1_relat_1 @ X0)
% 0.33/0.55          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.33/0.55          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 0.33/0.55      inference('sup-', [status(thm)], ['7', '22'])).
% 0.33/0.55  thf(t60_relat_1, conjecture,
% 0.33/0.55    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.33/0.55     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.33/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.33/0.55    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.33/0.55        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.33/0.55    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.33/0.55  thf('24', plain,
% 0.33/0.55      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.33/0.55        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.33/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.33/0.55  thf('25', plain,
% 0.33/0.55      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.33/0.55         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.33/0.55      inference('split', [status(esa)], ['24'])).
% 0.33/0.55  thf('26', plain,
% 0.33/0.55      (![X17 : $i, X20 : $i]:
% 0.33/0.55         (((X20) = (k1_relat_1 @ X17))
% 0.33/0.55          | (r2_hidden @ 
% 0.33/0.55             (k4_tarski @ (sk_C_1 @ X20 @ X17) @ (sk_D @ X20 @ X17)) @ X17)
% 0.33/0.55          | (r2_hidden @ (sk_C_1 @ X20 @ X17) @ X20))),
% 0.33/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.33/0.55  thf('27', plain,
% 0.33/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.33/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.33/0.55  thf('28', plain,
% 0.33/0.55      (![X0 : $i, X1 : $i]:
% 0.33/0.55         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.33/0.55          | ((X1) = (k1_relat_1 @ X0))
% 0.33/0.55          | ~ (v1_xboole_0 @ X0))),
% 0.33/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.33/0.55  thf('29', plain,
% 0.33/0.55      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.33/0.55      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.33/0.55  thf('30', plain,
% 0.33/0.55      (![X0 : $i, X1 : $i]:
% 0.33/0.55         (~ (v1_xboole_0 @ X1)
% 0.33/0.55          | ((X0) = (k1_relat_1 @ X1))
% 0.33/0.55          | ~ (v1_xboole_0 @ X0))),
% 0.33/0.55      inference('sup-', [status(thm)], ['28', '29'])).
% 0.33/0.55  thf('31', plain,
% 0.33/0.55      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.33/0.55         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.33/0.55      inference('split', [status(esa)], ['24'])).
% 0.33/0.55  thf('32', plain,
% 0.33/0.55      ((![X0 : $i]:
% 0.33/0.55          (((X0) != (k1_xboole_0))
% 0.33/0.55           | ~ (v1_xboole_0 @ X0)
% 0.33/0.55           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.33/0.55         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.33/0.55      inference('sup-', [status(thm)], ['30', '31'])).
% 0.33/0.55  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.33/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.33/0.55  thf('34', plain,
% 0.33/0.55      ((![X0 : $i]: (((X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.33/0.55         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.33/0.55      inference('demod', [status(thm)], ['32', '33'])).
% 0.33/0.55  thf('35', plain,
% 0.33/0.55      ((~ (v1_xboole_0 @ k1_xboole_0))
% 0.33/0.55         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.33/0.55      inference('simplify', [status(thm)], ['34'])).
% 0.33/0.55  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.33/0.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.33/0.55  thf('37', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.33/0.55      inference('simplify_reflect+', [status(thm)], ['35', '36'])).
% 0.33/0.55  thf('38', plain,
% 0.33/0.55      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.33/0.55       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.33/0.55      inference('split', [status(esa)], ['24'])).
% 0.33/0.55  thf('39', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.33/0.55      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.33/0.55  thf('40', plain, (((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.33/0.55      inference('simpl_trail', [status(thm)], ['25', '39'])).
% 0.33/0.55  thf('41', plain,
% 0.33/0.55      (![X0 : $i]:
% 0.33/0.55         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.33/0.55          | ~ (v1_relat_1 @ X0)
% 0.33/0.55          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.33/0.55      inference('simplify_reflect-', [status(thm)], ['23', '40'])).
% 0.33/0.55  thf(dt_k4_relat_1, axiom,
% 0.33/0.55    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.33/0.55  thf('42', plain,
% 0.33/0.55      (![X22 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X22)) | ~ (v1_relat_1 @ X22))),
% 0.33/0.55      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.33/0.55  thf('43', plain,
% 0.33/0.55      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.33/0.55      inference('clc', [status(thm)], ['41', '42'])).
% 0.33/0.55  thf('44', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.33/0.55      inference('sup-', [status(thm)], ['6', '43'])).
% 0.33/0.55  thf('45', plain, (![X14 : $i]: ((v1_relat_1 @ X14) | ~ (v1_xboole_0 @ X14))),
% 0.33/0.55      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.33/0.55  thf('46', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.33/0.55      inference('clc', [status(thm)], ['44', '45'])).
% 0.33/0.55  thf('47', plain, ($false), inference('sup-', [status(thm)], ['0', '46'])).
% 0.33/0.55  
% 0.33/0.55  % SZS output end Refutation
% 0.33/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
