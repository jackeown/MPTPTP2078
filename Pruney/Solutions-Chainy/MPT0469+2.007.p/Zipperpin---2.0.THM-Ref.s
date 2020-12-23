%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4pNR2hPOkC

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:17 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 144 expanded)
%              Number of leaves         :   25 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  424 ( 864 expanded)
%              Number of equality atoms :   46 (  80 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
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
    ! [X13: $i,X16: $i] :
      ( ( X16
        = ( k1_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X16 @ X13 ) @ ( sk_D @ X16 @ X13 ) ) @ X13 )
      | ( r2_hidden @ ( sk_C_1 @ X16 @ X13 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
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
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
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
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
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
    ! [X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

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

thf('15',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ( ( k2_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( k2_relat_1 @ X1 )
         != X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X1 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
        | ~ ( v1_relat_1 @ X0 )
        | ~ ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','19'])).

thf('21',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,
    ( ( ~ ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X10: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('25',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X18: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('27',plain,(
    ! [X20: $i] :
      ( ( ( k1_relat_1 @ X20 )
        = ( k2_relat_1 @ ( k4_relat_1 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
   <= ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','37'])).

thf('39',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('41',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k1_relat_1 @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('48',plain,(
    ( k2_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['38','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,(
    $false ),
    inference(demod,[status(thm)],['50','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4pNR2hPOkC
% 0.13/0.37  % Computer   : n002.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:50:52 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.24/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.56  % Solved by: fo/fo7.sh
% 0.24/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.56  % done 126 iterations in 0.070s
% 0.24/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.56  % SZS output start Refutation
% 0.24/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.24/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.56  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.24/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.24/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.56  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.24/0.56  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.24/0.56  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.24/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.56  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.24/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.56  thf(cc1_relat_1, axiom,
% 0.24/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.24/0.56  thf('0', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.24/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.24/0.56  thf(d4_relat_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.24/0.56       ( ![C:$i]:
% 0.24/0.56         ( ( r2_hidden @ C @ B ) <=>
% 0.24/0.56           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.24/0.56  thf('1', plain,
% 0.24/0.56      (![X13 : $i, X16 : $i]:
% 0.24/0.56         (((X16) = (k1_relat_1 @ X13))
% 0.24/0.56          | (r2_hidden @ 
% 0.24/0.56             (k4_tarski @ (sk_C_1 @ X16 @ X13) @ (sk_D @ X16 @ X13)) @ X13)
% 0.24/0.56          | (r2_hidden @ (sk_C_1 @ X16 @ X13) @ X16))),
% 0.24/0.56      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.24/0.56  thf(t2_boole, axiom,
% 0.24/0.56    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.24/0.56  thf('2', plain,
% 0.24/0.56      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.56      inference('cnf', [status(esa)], [t2_boole])).
% 0.24/0.56  thf(t4_xboole_0, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.56            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.24/0.56       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.24/0.56            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.24/0.56  thf('3', plain,
% 0.24/0.56      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.24/0.56         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.24/0.56          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.24/0.56      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.24/0.56  thf('4', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]:
% 0.24/0.56         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.56  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.24/0.56  thf('5', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.24/0.56  thf('6', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.24/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.56  thf('7', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 0.24/0.56          | ((X0) = (k1_relat_1 @ k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['1', '6'])).
% 0.24/0.56  thf('8', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.24/0.56      inference('demod', [status(thm)], ['4', '5'])).
% 0.24/0.56  thf('9', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.56  thf(t37_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_relat_1 @ A ) =>
% 0.24/0.56       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.24/0.56         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.24/0.56  thf('10', plain,
% 0.24/0.56      (![X20 : $i]:
% 0.24/0.56         (((k1_relat_1 @ X20) = (k2_relat_1 @ (k4_relat_1 @ X20)))
% 0.24/0.56          | ~ (v1_relat_1 @ X20))),
% 0.24/0.56      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.24/0.56  thf(t7_xboole_0, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.24/0.56          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.24/0.56  thf('11', plain,
% 0.24/0.56      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B_1 @ X7) @ X7))),
% 0.24/0.56      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.24/0.56  thf(d1_xboole_0, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.24/0.56  thf('12', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.24/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.24/0.56  thf('13', plain,
% 0.24/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.56  thf('14', plain,
% 0.24/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.56  thf(t60_relat_1, conjecture,
% 0.24/0.56    (( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.24/0.56     ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.24/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.56    (~( ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.24/0.56        ( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.24/0.56    inference('cnf.neg', [status(esa)], [t60_relat_1])).
% 0.24/0.56  thf('15', plain,
% 0.24/0.56      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))
% 0.24/0.56        | ((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('16', plain,
% 0.24/0.56      ((((k2_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.24/0.56         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('split', [status(esa)], ['15'])).
% 0.24/0.56  thf('17', plain,
% 0.24/0.56      ((![X0 : $i]:
% 0.24/0.56          (((k2_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.24/0.56         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['14', '16'])).
% 0.24/0.56  thf('18', plain,
% 0.24/0.56      ((![X0 : $i, X1 : $i]:
% 0.24/0.56          (((k2_relat_1 @ X1) != (X0))
% 0.24/0.56           | ~ (v1_xboole_0 @ X0)
% 0.24/0.56           | ~ (v1_xboole_0 @ X1)))
% 0.24/0.56         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['13', '17'])).
% 0.24/0.56  thf('19', plain,
% 0.24/0.56      ((![X1 : $i]:
% 0.24/0.56          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k2_relat_1 @ X1))))
% 0.24/0.56         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('simplify', [status(thm)], ['18'])).
% 0.24/0.56  thf('20', plain,
% 0.24/0.56      ((![X0 : $i]:
% 0.24/0.56          (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.24/0.56           | ~ (v1_relat_1 @ X0)
% 0.24/0.56           | ~ (v1_xboole_0 @ (k4_relat_1 @ X0))))
% 0.24/0.56         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['10', '19'])).
% 0.24/0.56  thf('21', plain,
% 0.24/0.56      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.56         | ~ (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))
% 0.24/0.56         | ~ (v1_relat_1 @ k1_xboole_0)))
% 0.24/0.56         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['9', '20'])).
% 0.24/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.56  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('23', plain,
% 0.24/0.56      (((~ (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))
% 0.24/0.56         | ~ (v1_relat_1 @ k1_xboole_0)))
% 0.24/0.56         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('demod', [status(thm)], ['21', '22'])).
% 0.24/0.56  thf('24', plain, (![X10 : $i]: ((v1_relat_1 @ X10) | ~ (v1_xboole_0 @ X10))),
% 0.24/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.24/0.56  thf('25', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.56  thf(dt_k4_relat_1, axiom,
% 0.24/0.56    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.24/0.56  thf('26', plain,
% 0.24/0.56      (![X18 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X18)) | ~ (v1_relat_1 @ X18))),
% 0.24/0.56      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.24/0.56  thf('27', plain,
% 0.24/0.56      (![X20 : $i]:
% 0.24/0.56         (((k1_relat_1 @ X20) = (k2_relat_1 @ (k4_relat_1 @ X20)))
% 0.24/0.56          | ~ (v1_relat_1 @ X20))),
% 0.24/0.56      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.24/0.56  thf(fc9_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.24/0.56       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.24/0.56  thf('28', plain,
% 0.24/0.56      (![X19 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ (k2_relat_1 @ X19))
% 0.24/0.56          | ~ (v1_relat_1 @ X19)
% 0.24/0.56          | (v1_xboole_0 @ X19))),
% 0.24/0.56      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.24/0.56  thf('29', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.24/0.56          | ~ (v1_relat_1 @ X0)
% 0.24/0.56          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.24/0.56          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.24/0.56  thf('30', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X0)
% 0.24/0.56          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.24/0.56          | ~ (v1_relat_1 @ X0)
% 0.24/0.56          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['26', '29'])).
% 0.24/0.56  thf('31', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.24/0.56          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.24/0.56          | ~ (v1_relat_1 @ X0))),
% 0.24/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.24/0.56  thf('32', plain,
% 0.24/0.56      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.56        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.24/0.56        | (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['25', '31'])).
% 0.24/0.56  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('34', plain,
% 0.24/0.56      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.24/0.56        | (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.24/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.24/0.56  thf('35', plain,
% 0.24/0.56      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.56        | (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['24', '34'])).
% 0.24/0.56  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('37', plain, ((v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))),
% 0.24/0.56      inference('demod', [status(thm)], ['35', '36'])).
% 0.24/0.56  thf('38', plain,
% 0.24/0.56      ((~ (v1_relat_1 @ k1_xboole_0))
% 0.24/0.56         <= (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('demod', [status(thm)], ['23', '37'])).
% 0.24/0.56  thf('39', plain, (((k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.56  thf('40', plain,
% 0.24/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.56  thf('41', plain,
% 0.24/0.56      ((((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0)))
% 0.24/0.56         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('split', [status(esa)], ['15'])).
% 0.24/0.56  thf('42', plain,
% 0.24/0.56      ((![X0 : $i]:
% 0.24/0.56          (((k1_relat_1 @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.24/0.56         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['40', '41'])).
% 0.24/0.56  thf('43', plain,
% 0.24/0.56      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.24/0.56         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['39', '42'])).
% 0.24/0.56  thf('44', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('45', plain,
% 0.24/0.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.24/0.56         <= (~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('demod', [status(thm)], ['43', '44'])).
% 0.24/0.56  thf('46', plain, ((((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.24/0.56      inference('simplify', [status(thm)], ['45'])).
% 0.24/0.56  thf('47', plain,
% 0.24/0.56      (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.24/0.56       ~ (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.24/0.56      inference('split', [status(esa)], ['15'])).
% 0.24/0.56  thf('48', plain, (~ (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.24/0.56      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 0.24/0.56  thf('49', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.24/0.56      inference('simpl_trail', [status(thm)], ['38', '48'])).
% 0.24/0.56  thf('50', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('sup-', [status(thm)], ['0', '49'])).
% 0.24/0.56  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('52', plain, ($false), inference('demod', [status(thm)], ['50', '51'])).
% 0.24/0.56  
% 0.24/0.56  % SZS output end Refutation
% 0.24/0.56  
% 0.24/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
