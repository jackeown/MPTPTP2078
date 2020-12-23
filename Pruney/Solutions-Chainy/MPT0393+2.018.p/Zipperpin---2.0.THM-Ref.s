%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hfo2BzVFSc

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:43 EST 2020

% Result     : Theorem 4.55s
% Output     : Refutation 4.55s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 140 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :   19
%              Number of atoms          :  539 (1386 expanded)
%              Number of equality atoms :   66 ( 162 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ( r2_hidden @ X8 @ X9 )
      | ( X9
       != ( k2_tarski @ X10 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('3',plain,(
    ! [X7: $i,X10: $i] :
      ( r2_hidden @ X7 @ ( k2_tarski @ X10 @ X7 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf(d1_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( A = k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ( B = k1_xboole_0 ) ) )
      & ( ( A != k1_xboole_0 )
       => ( ( B
            = ( k1_setfam_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ A )
                 => ( r2_hidden @ C @ D ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X29 @ X30 ) @ X29 )
      | ( r2_hidden @ ( sk_C_1 @ X29 @ X30 ) @ X31 )
      | ~ ( r2_hidden @ X31 @ X30 )
      | ( X29
        = ( k1_setfam_1 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(eq_fact,[status(thm)],['6'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('8',plain,(
    ! [X22: $i,X23: $i] :
      ( ( X23 != X22 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X22 ) )
       != ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('9',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X22 ) )
     != ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('11',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X25 @ X26 )
      | ~ ( r2_hidden @ X25 @ ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) @ X0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20
        = ( k1_tarski @ X19 ) )
      | ( X20 = k1_xboole_0 )
      | ~ ( r1_tarski @ X20 @ ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
        = ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X22: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X22 ) )
     != ( k1_tarski @ X22 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X22: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X22 ) ) ),
    inference(demod,[status(thm)],['9','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['7','21'])).

thf('23',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X29 @ X30 ) @ X29 )
      | ( r2_hidden @ ( sk_D_1 @ X29 @ X30 ) @ X30 )
      | ( X29
        = ( k1_setfam_1 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X22: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X22 ) ) ),
    inference(demod,[status(thm)],['9','20'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X23 ) @ ( k1_tarski @ X24 ) )
        = ( k1_tarski @ X23 ) )
      | ( X23 = X24 ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('29',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( X25 != X27 )
      | ~ ( r2_hidden @ X25 @ ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ~ ( r2_hidden @ X27 @ ( k4_xboole_0 @ X26 @ ( k1_tarski @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( sk_D_1 @ X0 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X29 @ X30 ) @ X29 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X29 @ X30 ) @ ( sk_D_1 @ X29 @ X30 ) )
      | ( X29
        = ( k1_setfam_1 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d1_setfam_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X22: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X22 ) ) ),
    inference(demod,[status(thm)],['9','20'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ ( k1_tarski @ X0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['7','21'])).

thf('39',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','39'])).

thf('41',plain,(
    $false ),
    inference(simplify,[status(thm)],['40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hfo2BzVFSc
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 4.55/4.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.55/4.76  % Solved by: fo/fo7.sh
% 4.55/4.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.55/4.76  % done 2103 iterations in 4.293s
% 4.55/4.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.55/4.76  % SZS output start Refutation
% 4.55/4.76  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 4.55/4.76  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.55/4.76  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 4.55/4.76  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.55/4.76  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 4.55/4.76  thf(sk_A_type, type, sk_A: $i).
% 4.55/4.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.55/4.76  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 4.55/4.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.55/4.76  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 4.55/4.76  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 4.55/4.76  thf(t11_setfam_1, conjecture,
% 4.55/4.76    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 4.55/4.76  thf(zf_stmt_0, negated_conjecture,
% 4.55/4.76    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 4.55/4.76    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 4.55/4.76  thf('0', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 4.55/4.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.55/4.76  thf(t69_enumset1, axiom,
% 4.55/4.76    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 4.55/4.76  thf('1', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 4.55/4.76      inference('cnf', [status(esa)], [t69_enumset1])).
% 4.55/4.76  thf(d2_tarski, axiom,
% 4.55/4.76    (![A:$i,B:$i,C:$i]:
% 4.55/4.76     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 4.55/4.76       ( ![D:$i]:
% 4.55/4.76         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 4.55/4.76  thf('2', plain,
% 4.55/4.76      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 4.55/4.76         (((X8) != (X7))
% 4.55/4.76          | (r2_hidden @ X8 @ X9)
% 4.55/4.76          | ((X9) != (k2_tarski @ X10 @ X7)))),
% 4.55/4.76      inference('cnf', [status(esa)], [d2_tarski])).
% 4.55/4.76  thf('3', plain,
% 4.55/4.76      (![X7 : $i, X10 : $i]: (r2_hidden @ X7 @ (k2_tarski @ X10 @ X7))),
% 4.55/4.76      inference('simplify', [status(thm)], ['2'])).
% 4.55/4.76  thf('4', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 4.55/4.76      inference('sup+', [status(thm)], ['1', '3'])).
% 4.55/4.76  thf(d1_setfam_1, axiom,
% 4.55/4.76    (![A:$i,B:$i]:
% 4.55/4.76     ( ( ( ( A ) = ( k1_xboole_0 ) ) =>
% 4.55/4.76         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=> ( ( B ) = ( k1_xboole_0 ) ) ) ) & 
% 4.55/4.76       ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 4.55/4.76         ( ( ( B ) = ( k1_setfam_1 @ A ) ) <=>
% 4.55/4.76           ( ![C:$i]:
% 4.55/4.76             ( ( r2_hidden @ C @ B ) <=>
% 4.55/4.76               ( ![D:$i]: ( ( r2_hidden @ D @ A ) => ( r2_hidden @ C @ D ) ) ) ) ) ) ) ))).
% 4.55/4.76  thf('5', plain,
% 4.55/4.76      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.55/4.76         ((r2_hidden @ (sk_C_1 @ X29 @ X30) @ X29)
% 4.55/4.76          | (r2_hidden @ (sk_C_1 @ X29 @ X30) @ X31)
% 4.55/4.76          | ~ (r2_hidden @ X31 @ X30)
% 4.55/4.76          | ((X29) = (k1_setfam_1 @ X30))
% 4.55/4.76          | ((X30) = (k1_xboole_0)))),
% 4.55/4.76      inference('cnf', [status(esa)], [d1_setfam_1])).
% 4.55/4.76  thf('6', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i]:
% 4.55/4.76         (((k1_tarski @ X0) = (k1_xboole_0))
% 4.55/4.76          | ((X1) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 4.55/4.76          | (r2_hidden @ (sk_C_1 @ X1 @ (k1_tarski @ X0)) @ X0)
% 4.55/4.76          | (r2_hidden @ (sk_C_1 @ X1 @ (k1_tarski @ X0)) @ X1))),
% 4.55/4.76      inference('sup-', [status(thm)], ['4', '5'])).
% 4.55/4.76  thf('7', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         ((r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0)
% 4.55/4.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 4.55/4.76          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 4.55/4.76      inference('eq_fact', [status(thm)], ['6'])).
% 4.55/4.76  thf(t20_zfmisc_1, axiom,
% 4.55/4.76    (![A:$i,B:$i]:
% 4.55/4.76     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 4.55/4.76         ( k1_tarski @ A ) ) <=>
% 4.55/4.76       ( ( A ) != ( B ) ) ))).
% 4.55/4.76  thf('8', plain,
% 4.55/4.76      (![X22 : $i, X23 : $i]:
% 4.55/4.76         (((X23) != (X22))
% 4.55/4.76          | ((k4_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X22))
% 4.55/4.76              != (k1_tarski @ X23)))),
% 4.55/4.76      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 4.55/4.76  thf('9', plain,
% 4.55/4.76      (![X22 : $i]:
% 4.55/4.76         ((k4_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X22))
% 4.55/4.76           != (k1_tarski @ X22))),
% 4.55/4.76      inference('simplify', [status(thm)], ['8'])).
% 4.55/4.76  thf(d3_tarski, axiom,
% 4.55/4.76    (![A:$i,B:$i]:
% 4.55/4.76     ( ( r1_tarski @ A @ B ) <=>
% 4.55/4.76       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.55/4.76  thf('10', plain,
% 4.55/4.76      (![X1 : $i, X3 : $i]:
% 4.55/4.76         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.55/4.76      inference('cnf', [status(esa)], [d3_tarski])).
% 4.55/4.76  thf(t64_zfmisc_1, axiom,
% 4.55/4.76    (![A:$i,B:$i,C:$i]:
% 4.55/4.76     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 4.55/4.76       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 4.55/4.76  thf('11', plain,
% 4.55/4.76      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.55/4.76         ((r2_hidden @ X25 @ X26)
% 4.55/4.76          | ~ (r2_hidden @ X25 @ (k4_xboole_0 @ X26 @ (k1_tarski @ X27))))),
% 4.55/4.76      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 4.55/4.76  thf('12', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.55/4.76         ((r1_tarski @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X2)
% 4.55/4.76          | (r2_hidden @ (sk_C @ X2 @ (k4_xboole_0 @ X1 @ (k1_tarski @ X0))) @ 
% 4.55/4.76             X1))),
% 4.55/4.76      inference('sup-', [status(thm)], ['10', '11'])).
% 4.55/4.76  thf('13', plain,
% 4.55/4.76      (![X1 : $i, X3 : $i]:
% 4.55/4.76         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.55/4.76      inference('cnf', [status(esa)], [d3_tarski])).
% 4.55/4.76  thf('14', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i]:
% 4.55/4.76         ((r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)
% 4.55/4.76          | (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0))),
% 4.55/4.76      inference('sup-', [status(thm)], ['12', '13'])).
% 4.55/4.76  thf('15', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i]:
% 4.55/4.76         (r1_tarski @ (k4_xboole_0 @ X0 @ (k1_tarski @ X1)) @ X0)),
% 4.55/4.76      inference('simplify', [status(thm)], ['14'])).
% 4.55/4.76  thf(l3_zfmisc_1, axiom,
% 4.55/4.76    (![A:$i,B:$i]:
% 4.55/4.76     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 4.55/4.76       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 4.55/4.76  thf('16', plain,
% 4.55/4.76      (![X19 : $i, X20 : $i]:
% 4.55/4.76         (((X20) = (k1_tarski @ X19))
% 4.55/4.76          | ((X20) = (k1_xboole_0))
% 4.55/4.76          | ~ (r1_tarski @ X20 @ (k1_tarski @ X19)))),
% 4.55/4.76      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 4.55/4.76  thf('17', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i]:
% 4.55/4.76         (((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)) = (k1_xboole_0))
% 4.55/4.76          | ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 4.55/4.76              = (k1_tarski @ X0)))),
% 4.55/4.76      inference('sup-', [status(thm)], ['15', '16'])).
% 4.55/4.76  thf('18', plain,
% 4.55/4.76      (![X22 : $i]:
% 4.55/4.76         ((k4_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X22))
% 4.55/4.76           != (k1_tarski @ X22))),
% 4.55/4.76      inference('simplify', [status(thm)], ['8'])).
% 4.55/4.76  thf('19', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 4.55/4.76          | ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0))
% 4.55/4.76              = (k1_xboole_0)))),
% 4.55/4.76      inference('sup-', [status(thm)], ['17', '18'])).
% 4.55/4.76  thf('20', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)) = (k1_xboole_0))),
% 4.55/4.76      inference('simplify', [status(thm)], ['19'])).
% 4.55/4.76  thf('21', plain, (![X22 : $i]: ((k1_xboole_0) != (k1_tarski @ X22))),
% 4.55/4.76      inference('demod', [status(thm)], ['9', '20'])).
% 4.55/4.76  thf('22', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 4.55/4.76          | (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0))),
% 4.55/4.76      inference('clc', [status(thm)], ['7', '21'])).
% 4.55/4.76  thf('23', plain,
% 4.55/4.76      (![X29 : $i, X30 : $i]:
% 4.55/4.76         (~ (r2_hidden @ (sk_C_1 @ X29 @ X30) @ X29)
% 4.55/4.76          | (r2_hidden @ (sk_D_1 @ X29 @ X30) @ X30)
% 4.55/4.76          | ((X29) = (k1_setfam_1 @ X30))
% 4.55/4.76          | ((X30) = (k1_xboole_0)))),
% 4.55/4.76      inference('cnf', [status(esa)], [d1_setfam_1])).
% 4.55/4.76  thf('24', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 4.55/4.76          | ((k1_tarski @ X0) = (k1_xboole_0))
% 4.55/4.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 4.55/4.76          | (r2_hidden @ (sk_D_1 @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0)))),
% 4.55/4.76      inference('sup-', [status(thm)], ['22', '23'])).
% 4.55/4.76  thf('25', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         ((r2_hidden @ (sk_D_1 @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0))
% 4.55/4.76          | ((k1_tarski @ X0) = (k1_xboole_0))
% 4.55/4.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 4.55/4.76      inference('simplify', [status(thm)], ['24'])).
% 4.55/4.76  thf('26', plain, (![X22 : $i]: ((k1_xboole_0) != (k1_tarski @ X22))),
% 4.55/4.76      inference('demod', [status(thm)], ['9', '20'])).
% 4.55/4.76  thf('27', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 4.55/4.76          | (r2_hidden @ (sk_D_1 @ X0 @ (k1_tarski @ X0)) @ (k1_tarski @ X0)))),
% 4.55/4.76      inference('clc', [status(thm)], ['25', '26'])).
% 4.55/4.76  thf('28', plain,
% 4.55/4.76      (![X23 : $i, X24 : $i]:
% 4.55/4.76         (((k4_xboole_0 @ (k1_tarski @ X23) @ (k1_tarski @ X24))
% 4.55/4.76            = (k1_tarski @ X23))
% 4.55/4.76          | ((X23) = (X24)))),
% 4.55/4.76      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 4.55/4.76  thf('29', plain,
% 4.55/4.76      (![X25 : $i, X26 : $i, X27 : $i]:
% 4.55/4.76         (((X25) != (X27))
% 4.55/4.76          | ~ (r2_hidden @ X25 @ (k4_xboole_0 @ X26 @ (k1_tarski @ X27))))),
% 4.55/4.76      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 4.55/4.76  thf('30', plain,
% 4.55/4.76      (![X26 : $i, X27 : $i]:
% 4.55/4.76         ~ (r2_hidden @ X27 @ (k4_xboole_0 @ X26 @ (k1_tarski @ X27)))),
% 4.55/4.76      inference('simplify', [status(thm)], ['29'])).
% 4.55/4.76  thf('31', plain,
% 4.55/4.76      (![X0 : $i, X1 : $i]:
% 4.55/4.76         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 4.55/4.76      inference('sup-', [status(thm)], ['28', '30'])).
% 4.55/4.76  thf('32', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 4.55/4.76          | ((X0) = (sk_D_1 @ X0 @ (k1_tarski @ X0))))),
% 4.55/4.76      inference('sup-', [status(thm)], ['27', '31'])).
% 4.55/4.76  thf('33', plain,
% 4.55/4.76      (![X29 : $i, X30 : $i]:
% 4.55/4.76         (~ (r2_hidden @ (sk_C_1 @ X29 @ X30) @ X29)
% 4.55/4.76          | ~ (r2_hidden @ (sk_C_1 @ X29 @ X30) @ (sk_D_1 @ X29 @ X30))
% 4.55/4.76          | ((X29) = (k1_setfam_1 @ X30))
% 4.55/4.76          | ((X30) = (k1_xboole_0)))),
% 4.55/4.76      inference('cnf', [status(esa)], [d1_setfam_1])).
% 4.55/4.76  thf('34', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0)
% 4.55/4.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 4.55/4.76          | ((k1_tarski @ X0) = (k1_xboole_0))
% 4.55/4.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 4.55/4.76          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0))),
% 4.55/4.76      inference('sup-', [status(thm)], ['32', '33'])).
% 4.55/4.76  thf('35', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (((k1_tarski @ X0) = (k1_xboole_0))
% 4.55/4.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 4.55/4.76          | ~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0))),
% 4.55/4.76      inference('simplify', [status(thm)], ['34'])).
% 4.55/4.76  thf('36', plain, (![X22 : $i]: ((k1_xboole_0) != (k1_tarski @ X22))),
% 4.55/4.76      inference('demod', [status(thm)], ['9', '20'])).
% 4.55/4.76  thf('37', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (~ (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0)
% 4.55/4.76          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 4.55/4.76      inference('clc', [status(thm)], ['35', '36'])).
% 4.55/4.76  thf('38', plain,
% 4.55/4.76      (![X0 : $i]:
% 4.55/4.76         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 4.55/4.76          | (r2_hidden @ (sk_C_1 @ X0 @ (k1_tarski @ X0)) @ X0))),
% 4.55/4.76      inference('clc', [status(thm)], ['7', '21'])).
% 4.55/4.76  thf('39', plain, (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))),
% 4.55/4.76      inference('clc', [status(thm)], ['37', '38'])).
% 4.55/4.76  thf('40', plain, (((sk_A) != (sk_A))),
% 4.55/4.76      inference('demod', [status(thm)], ['0', '39'])).
% 4.55/4.76  thf('41', plain, ($false), inference('simplify', [status(thm)], ['40'])).
% 4.55/4.76  
% 4.55/4.76  % SZS output end Refutation
% 4.55/4.76  
% 4.55/4.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
