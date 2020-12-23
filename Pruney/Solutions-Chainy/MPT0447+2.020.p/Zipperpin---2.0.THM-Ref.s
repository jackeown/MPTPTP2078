%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.55dmY9NHKy

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:55 EST 2020

% Result     : Theorem 1.60s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   69 (  94 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   16
%              Number of atoms          :  476 ( 764 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i] :
      ( ( ( k3_relat_1 @ X26 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X26 ) @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X26: $i] :
      ( ( ( k3_relat_1 @ X26 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X26 ) @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('3',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( r1_tarski @ ( k2_relat_1 @ X28 ) @ ( k2_relat_1 @ X27 ) )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X4 @ ( k2_xboole_0 @ X6 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('15',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( r1_tarski @ ( k1_relat_1 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['14','22'])).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ X23 @ ( sk_D_1 @ X23 @ X21 ) ) @ X21 )
      | ( X22
       != ( k1_relat_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('26',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X23 @ ( sk_D_1 @ X23 @ X21 ) ) @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('28',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X30 ) @ X31 )
      | ( r2_hidden @ X29 @ ( k3_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['23','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('39',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['39'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X9 @ X8 )
      | ( r1_tarski @ ( k2_xboole_0 @ X7 @ X9 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['13','42'])).

thf('44',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.55dmY9NHKy
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:28:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 1.60/1.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.60/1.77  % Solved by: fo/fo7.sh
% 1.60/1.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.60/1.77  % done 1585 iterations in 1.308s
% 1.60/1.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.60/1.77  % SZS output start Refutation
% 1.60/1.77  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.60/1.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.60/1.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.60/1.77  thf(sk_A_type, type, sk_A: $i).
% 1.60/1.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.60/1.77  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.60/1.77  thf(sk_B_type, type, sk_B: $i).
% 1.60/1.77  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.60/1.77  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.60/1.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.60/1.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.60/1.77  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.60/1.77  thf(t31_relat_1, conjecture,
% 1.60/1.77    (![A:$i]:
% 1.60/1.77     ( ( v1_relat_1 @ A ) =>
% 1.60/1.77       ( ![B:$i]:
% 1.60/1.77         ( ( v1_relat_1 @ B ) =>
% 1.60/1.77           ( ( r1_tarski @ A @ B ) =>
% 1.60/1.77             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.60/1.77  thf(zf_stmt_0, negated_conjecture,
% 1.60/1.77    (~( ![A:$i]:
% 1.60/1.77        ( ( v1_relat_1 @ A ) =>
% 1.60/1.77          ( ![B:$i]:
% 1.60/1.77            ( ( v1_relat_1 @ B ) =>
% 1.60/1.77              ( ( r1_tarski @ A @ B ) =>
% 1.60/1.77                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 1.60/1.77    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 1.60/1.77  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf(d6_relat_1, axiom,
% 1.60/1.77    (![A:$i]:
% 1.60/1.77     ( ( v1_relat_1 @ A ) =>
% 1.60/1.77       ( ( k3_relat_1 @ A ) =
% 1.60/1.77         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.60/1.77  thf('1', plain,
% 1.60/1.77      (![X26 : $i]:
% 1.60/1.77         (((k3_relat_1 @ X26)
% 1.60/1.77            = (k2_xboole_0 @ (k1_relat_1 @ X26) @ (k2_relat_1 @ X26)))
% 1.60/1.77          | ~ (v1_relat_1 @ X26))),
% 1.60/1.77      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.60/1.77  thf('2', plain,
% 1.60/1.77      (![X26 : $i]:
% 1.60/1.77         (((k3_relat_1 @ X26)
% 1.60/1.77            = (k2_xboole_0 @ (k1_relat_1 @ X26) @ (k2_relat_1 @ X26)))
% 1.60/1.77          | ~ (v1_relat_1 @ X26))),
% 1.60/1.77      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.60/1.77  thf('3', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf(t25_relat_1, axiom,
% 1.60/1.77    (![A:$i]:
% 1.60/1.77     ( ( v1_relat_1 @ A ) =>
% 1.60/1.77       ( ![B:$i]:
% 1.60/1.77         ( ( v1_relat_1 @ B ) =>
% 1.60/1.77           ( ( r1_tarski @ A @ B ) =>
% 1.60/1.77             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.60/1.77               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.60/1.77  thf('4', plain,
% 1.60/1.77      (![X27 : $i, X28 : $i]:
% 1.60/1.77         (~ (v1_relat_1 @ X27)
% 1.60/1.77          | (r1_tarski @ (k2_relat_1 @ X28) @ (k2_relat_1 @ X27))
% 1.60/1.77          | ~ (r1_tarski @ X28 @ X27)
% 1.60/1.77          | ~ (v1_relat_1 @ X28))),
% 1.60/1.77      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.60/1.77  thf('5', plain,
% 1.60/1.77      ((~ (v1_relat_1 @ sk_A)
% 1.60/1.77        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.60/1.77        | ~ (v1_relat_1 @ sk_B))),
% 1.60/1.77      inference('sup-', [status(thm)], ['3', '4'])).
% 1.60/1.77  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('8', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 1.60/1.77      inference('demod', [status(thm)], ['5', '6', '7'])).
% 1.60/1.77  thf(t10_xboole_1, axiom,
% 1.60/1.77    (![A:$i,B:$i,C:$i]:
% 1.60/1.77     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 1.60/1.77  thf('9', plain,
% 1.60/1.77      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.60/1.77         (~ (r1_tarski @ X4 @ X5) | (r1_tarski @ X4 @ (k2_xboole_0 @ X6 @ X5)))),
% 1.60/1.77      inference('cnf', [status(esa)], [t10_xboole_1])).
% 1.60/1.77  thf('10', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         (r1_tarski @ (k2_relat_1 @ sk_A) @ 
% 1.60/1.77          (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['8', '9'])).
% 1.60/1.77  thf('11', plain,
% 1.60/1.77      (((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.60/1.77        | ~ (v1_relat_1 @ sk_B))),
% 1.60/1.77      inference('sup+', [status(thm)], ['2', '10'])).
% 1.60/1.77  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('13', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.60/1.77      inference('demod', [status(thm)], ['11', '12'])).
% 1.60/1.77  thf(d3_tarski, axiom,
% 1.60/1.77    (![A:$i,B:$i]:
% 1.60/1.77     ( ( r1_tarski @ A @ B ) <=>
% 1.60/1.77       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.60/1.77  thf('14', plain,
% 1.60/1.77      (![X1 : $i, X3 : $i]:
% 1.60/1.77         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.60/1.77      inference('cnf', [status(esa)], [d3_tarski])).
% 1.60/1.77  thf('15', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('16', plain,
% 1.60/1.77      (![X27 : $i, X28 : $i]:
% 1.60/1.77         (~ (v1_relat_1 @ X27)
% 1.60/1.77          | (r1_tarski @ (k1_relat_1 @ X28) @ (k1_relat_1 @ X27))
% 1.60/1.77          | ~ (r1_tarski @ X28 @ X27)
% 1.60/1.77          | ~ (v1_relat_1 @ X28))),
% 1.60/1.77      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.60/1.77  thf('17', plain,
% 1.60/1.77      ((~ (v1_relat_1 @ sk_A)
% 1.60/1.77        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.60/1.77        | ~ (v1_relat_1 @ sk_B))),
% 1.60/1.77      inference('sup-', [status(thm)], ['15', '16'])).
% 1.60/1.77  thf('18', plain, ((v1_relat_1 @ sk_A)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('20', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 1.60/1.77      inference('demod', [status(thm)], ['17', '18', '19'])).
% 1.60/1.77  thf('21', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.77         (~ (r2_hidden @ X0 @ X1)
% 1.60/1.77          | (r2_hidden @ X0 @ X2)
% 1.60/1.77          | ~ (r1_tarski @ X1 @ X2))),
% 1.60/1.77      inference('cnf', [status(esa)], [d3_tarski])).
% 1.60/1.77  thf('22', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((r2_hidden @ X0 @ (k1_relat_1 @ sk_B))
% 1.60/1.77          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_A)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['20', '21'])).
% 1.60/1.77  thf('23', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 1.60/1.77          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ 
% 1.60/1.77             (k1_relat_1 @ sk_B)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['14', '22'])).
% 1.60/1.77  thf('24', plain,
% 1.60/1.77      (![X1 : $i, X3 : $i]:
% 1.60/1.77         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.60/1.77      inference('cnf', [status(esa)], [d3_tarski])).
% 1.60/1.77  thf(d4_relat_1, axiom,
% 1.60/1.77    (![A:$i,B:$i]:
% 1.60/1.77     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 1.60/1.77       ( ![C:$i]:
% 1.60/1.77         ( ( r2_hidden @ C @ B ) <=>
% 1.60/1.77           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 1.60/1.77  thf('25', plain,
% 1.60/1.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.60/1.77         (~ (r2_hidden @ X23 @ X22)
% 1.60/1.77          | (r2_hidden @ (k4_tarski @ X23 @ (sk_D_1 @ X23 @ X21)) @ X21)
% 1.60/1.77          | ((X22) != (k1_relat_1 @ X21)))),
% 1.60/1.77      inference('cnf', [status(esa)], [d4_relat_1])).
% 1.60/1.77  thf('26', plain,
% 1.60/1.77      (![X21 : $i, X23 : $i]:
% 1.60/1.77         ((r2_hidden @ (k4_tarski @ X23 @ (sk_D_1 @ X23 @ X21)) @ X21)
% 1.60/1.77          | ~ (r2_hidden @ X23 @ (k1_relat_1 @ X21)))),
% 1.60/1.77      inference('simplify', [status(thm)], ['25'])).
% 1.60/1.77  thf('27', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.60/1.77          | (r2_hidden @ 
% 1.60/1.77             (k4_tarski @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ 
% 1.60/1.77              (sk_D_1 @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ X0)) @ 
% 1.60/1.77             X0))),
% 1.60/1.77      inference('sup-', [status(thm)], ['24', '26'])).
% 1.60/1.77  thf(t30_relat_1, axiom,
% 1.60/1.77    (![A:$i,B:$i,C:$i]:
% 1.60/1.77     ( ( v1_relat_1 @ C ) =>
% 1.60/1.77       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 1.60/1.77         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 1.60/1.77           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 1.60/1.77  thf('28', plain,
% 1.60/1.77      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.60/1.77         (~ (r2_hidden @ (k4_tarski @ X29 @ X30) @ X31)
% 1.60/1.77          | (r2_hidden @ X29 @ (k3_relat_1 @ X31))
% 1.60/1.77          | ~ (v1_relat_1 @ X31))),
% 1.60/1.77      inference('cnf', [status(esa)], [t30_relat_1])).
% 1.60/1.77  thf('29', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         ((r1_tarski @ (k1_relat_1 @ X0) @ X1)
% 1.60/1.77          | ~ (v1_relat_1 @ X0)
% 1.60/1.77          | (r2_hidden @ (sk_C @ X1 @ (k1_relat_1 @ X0)) @ (k3_relat_1 @ X0)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['27', '28'])).
% 1.60/1.77  thf('30', plain,
% 1.60/1.77      (![X1 : $i, X3 : $i]:
% 1.60/1.77         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.60/1.77      inference('cnf', [status(esa)], [d3_tarski])).
% 1.60/1.77  thf('31', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         (~ (v1_relat_1 @ X0)
% 1.60/1.77          | (r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.60/1.77          | (r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['29', '30'])).
% 1.60/1.77  thf('32', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.60/1.77          | ~ (v1_relat_1 @ X0))),
% 1.60/1.77      inference('simplify', [status(thm)], ['31'])).
% 1.60/1.77  thf('33', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.60/1.77         (~ (r2_hidden @ X0 @ X1)
% 1.60/1.77          | (r2_hidden @ X0 @ X2)
% 1.60/1.77          | ~ (r1_tarski @ X1 @ X2))),
% 1.60/1.77      inference('cnf', [status(esa)], [d3_tarski])).
% 1.60/1.77  thf('34', plain,
% 1.60/1.77      (![X0 : $i, X1 : $i]:
% 1.60/1.77         (~ (v1_relat_1 @ X0)
% 1.60/1.77          | (r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 1.60/1.77          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['32', '33'])).
% 1.60/1.77  thf('35', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 1.60/1.77          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ 
% 1.60/1.77             (k3_relat_1 @ sk_B))
% 1.60/1.77          | ~ (v1_relat_1 @ sk_B))),
% 1.60/1.77      inference('sup-', [status(thm)], ['23', '34'])).
% 1.60/1.77  thf('36', plain, ((v1_relat_1 @ sk_B)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('37', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 1.60/1.77          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_A)) @ 
% 1.60/1.77             (k3_relat_1 @ sk_B)))),
% 1.60/1.77      inference('demod', [status(thm)], ['35', '36'])).
% 1.60/1.77  thf('38', plain,
% 1.60/1.77      (![X1 : $i, X3 : $i]:
% 1.60/1.77         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.60/1.77      inference('cnf', [status(esa)], [d3_tarski])).
% 1.60/1.77  thf('39', plain,
% 1.60/1.77      (((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.60/1.77        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['37', '38'])).
% 1.60/1.77  thf('40', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.60/1.77      inference('simplify', [status(thm)], ['39'])).
% 1.60/1.77  thf(t8_xboole_1, axiom,
% 1.60/1.77    (![A:$i,B:$i,C:$i]:
% 1.60/1.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.60/1.77       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.60/1.77  thf('41', plain,
% 1.60/1.77      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.60/1.77         (~ (r1_tarski @ X7 @ X8)
% 1.60/1.77          | ~ (r1_tarski @ X9 @ X8)
% 1.60/1.77          | (r1_tarski @ (k2_xboole_0 @ X7 @ X9) @ X8))),
% 1.60/1.77      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.60/1.77  thf('42', plain,
% 1.60/1.77      (![X0 : $i]:
% 1.60/1.77         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 1.60/1.77           (k3_relat_1 @ sk_B))
% 1.60/1.77          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 1.60/1.77      inference('sup-', [status(thm)], ['40', '41'])).
% 1.60/1.77  thf('43', plain,
% 1.60/1.77      ((r1_tarski @ 
% 1.60/1.77        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 1.60/1.77        (k3_relat_1 @ sk_B))),
% 1.60/1.77      inference('sup-', [status(thm)], ['13', '42'])).
% 1.60/1.77  thf('44', plain,
% 1.60/1.77      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.60/1.77        | ~ (v1_relat_1 @ sk_A))),
% 1.60/1.77      inference('sup+', [status(thm)], ['1', '43'])).
% 1.60/1.77  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 1.60/1.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.60/1.77  thf('46', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.60/1.77      inference('demod', [status(thm)], ['44', '45'])).
% 1.60/1.77  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 1.60/1.77  
% 1.60/1.77  % SZS output end Refutation
% 1.60/1.77  
% 1.62/1.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
