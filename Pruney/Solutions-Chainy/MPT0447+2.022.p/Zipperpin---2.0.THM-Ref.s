%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fJaro3v3GL

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:55 EST 2020

% Result     : Theorem 4.37s
% Output     : Refutation 4.37s
% Verified   : 
% Statistics : Number of formulae       :   65 (  87 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  423 ( 684 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X23 @ X21 ) @ X23 ) @ X21 )
      | ( X22
       != ( k2_relat_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('4',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X23 @ X21 ) @ X23 ) @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k2_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X29 @ X30 ) @ X31 )
      | ( r2_hidden @ X30 @ ( k3_relat_1 @ X31 ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( r1_tarski @ ( k2_relat_1 @ X28 ) @ ( k2_relat_1 @ X27 ) )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X26: $i] :
      ( ( ( k3_relat_1 @ X26 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X26 ) @ ( k2_relat_1 @ X26 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i] :
      ( r1_tarski @ X7 @ ( k2_xboole_0 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( v1_relat_1 @ X27 )
      | ( r1_tarski @ ( k1_relat_1 @ X28 ) @ ( k1_relat_1 @ X27 ) )
      | ~ ( r1_tarski @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X11 @ X10 )
      | ( r1_tarski @ ( k2_xboole_0 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['21','37'])).

thf('39',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['0','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fJaro3v3GL
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:43:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 4.37/4.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.37/4.60  % Solved by: fo/fo7.sh
% 4.37/4.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.37/4.60  % done 2945 iterations in 4.140s
% 4.37/4.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.37/4.60  % SZS output start Refutation
% 4.37/4.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 4.37/4.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 4.37/4.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.37/4.60  thf(sk_B_type, type, sk_B: $i).
% 4.37/4.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 4.37/4.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.37/4.60  thf(sk_A_type, type, sk_A: $i).
% 4.37/4.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 4.37/4.60  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 4.37/4.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.37/4.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 4.37/4.60  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 4.37/4.60  thf(t31_relat_1, conjecture,
% 4.37/4.60    (![A:$i]:
% 4.37/4.60     ( ( v1_relat_1 @ A ) =>
% 4.37/4.60       ( ![B:$i]:
% 4.37/4.60         ( ( v1_relat_1 @ B ) =>
% 4.37/4.60           ( ( r1_tarski @ A @ B ) =>
% 4.37/4.60             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 4.37/4.60  thf(zf_stmt_0, negated_conjecture,
% 4.37/4.60    (~( ![A:$i]:
% 4.37/4.60        ( ( v1_relat_1 @ A ) =>
% 4.37/4.60          ( ![B:$i]:
% 4.37/4.60            ( ( v1_relat_1 @ B ) =>
% 4.37/4.60              ( ( r1_tarski @ A @ B ) =>
% 4.37/4.60                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 4.37/4.60    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 4.37/4.60  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.37/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.60  thf(d6_relat_1, axiom,
% 4.37/4.60    (![A:$i]:
% 4.37/4.60     ( ( v1_relat_1 @ A ) =>
% 4.37/4.60       ( ( k3_relat_1 @ A ) =
% 4.37/4.60         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 4.37/4.60  thf('1', plain,
% 4.37/4.60      (![X26 : $i]:
% 4.37/4.60         (((k3_relat_1 @ X26)
% 4.37/4.60            = (k2_xboole_0 @ (k1_relat_1 @ X26) @ (k2_relat_1 @ X26)))
% 4.37/4.60          | ~ (v1_relat_1 @ X26))),
% 4.37/4.60      inference('cnf', [status(esa)], [d6_relat_1])).
% 4.37/4.60  thf(d3_tarski, axiom,
% 4.37/4.60    (![A:$i,B:$i]:
% 4.37/4.60     ( ( r1_tarski @ A @ B ) <=>
% 4.37/4.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 4.37/4.60  thf('2', plain,
% 4.37/4.60      (![X1 : $i, X3 : $i]:
% 4.37/4.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 4.37/4.60      inference('cnf', [status(esa)], [d3_tarski])).
% 4.37/4.60  thf(d5_relat_1, axiom,
% 4.37/4.60    (![A:$i,B:$i]:
% 4.37/4.60     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 4.37/4.60       ( ![C:$i]:
% 4.37/4.60         ( ( r2_hidden @ C @ B ) <=>
% 4.37/4.60           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 4.37/4.60  thf('3', plain,
% 4.37/4.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.37/4.60         (~ (r2_hidden @ X23 @ X22)
% 4.37/4.60          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X23 @ X21) @ X23) @ X21)
% 4.37/4.60          | ((X22) != (k2_relat_1 @ X21)))),
% 4.37/4.60      inference('cnf', [status(esa)], [d5_relat_1])).
% 4.37/4.60  thf('4', plain,
% 4.37/4.60      (![X21 : $i, X23 : $i]:
% 4.37/4.60         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X23 @ X21) @ X23) @ X21)
% 4.37/4.60          | ~ (r2_hidden @ X23 @ (k2_relat_1 @ X21)))),
% 4.37/4.60      inference('simplify', [status(thm)], ['3'])).
% 4.37/4.60  thf('5', plain,
% 4.37/4.60      (![X0 : $i, X1 : $i]:
% 4.37/4.60         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 4.37/4.60          | (r2_hidden @ 
% 4.37/4.60             (k4_tarski @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 4.37/4.60              (sk_C @ X1 @ (k2_relat_1 @ X0))) @ 
% 4.37/4.60             X0))),
% 4.37/4.60      inference('sup-', [status(thm)], ['2', '4'])).
% 4.37/4.60  thf(t30_relat_1, axiom,
% 4.37/4.60    (![A:$i,B:$i,C:$i]:
% 4.37/4.60     ( ( v1_relat_1 @ C ) =>
% 4.37/4.60       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 4.37/4.60         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 4.37/4.60           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 4.37/4.60  thf('6', plain,
% 4.37/4.60      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.37/4.60         (~ (r2_hidden @ (k4_tarski @ X29 @ X30) @ X31)
% 4.37/4.60          | (r2_hidden @ X30 @ (k3_relat_1 @ X31))
% 4.37/4.60          | ~ (v1_relat_1 @ X31))),
% 4.37/4.60      inference('cnf', [status(esa)], [t30_relat_1])).
% 4.37/4.60  thf('7', plain,
% 4.37/4.60      (![X0 : $i, X1 : $i]:
% 4.37/4.60         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 4.37/4.60          | ~ (v1_relat_1 @ X0)
% 4.37/4.60          | (r2_hidden @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ (k3_relat_1 @ X0)))),
% 4.37/4.60      inference('sup-', [status(thm)], ['5', '6'])).
% 4.37/4.60  thf('8', plain,
% 4.37/4.60      (![X1 : $i, X3 : $i]:
% 4.37/4.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 4.37/4.60      inference('cnf', [status(esa)], [d3_tarski])).
% 4.37/4.60  thf('9', plain,
% 4.37/4.60      (![X0 : $i]:
% 4.37/4.60         (~ (v1_relat_1 @ X0)
% 4.37/4.60          | (r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 4.37/4.60          | (r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0)))),
% 4.37/4.60      inference('sup-', [status(thm)], ['7', '8'])).
% 4.37/4.60  thf('10', plain,
% 4.37/4.60      (![X0 : $i]:
% 4.37/4.60         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 4.37/4.60          | ~ (v1_relat_1 @ X0))),
% 4.37/4.60      inference('simplify', [status(thm)], ['9'])).
% 4.37/4.60  thf('11', plain, ((r1_tarski @ sk_A @ sk_B)),
% 4.37/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.60  thf(t25_relat_1, axiom,
% 4.37/4.60    (![A:$i]:
% 4.37/4.60     ( ( v1_relat_1 @ A ) =>
% 4.37/4.60       ( ![B:$i]:
% 4.37/4.60         ( ( v1_relat_1 @ B ) =>
% 4.37/4.60           ( ( r1_tarski @ A @ B ) =>
% 4.37/4.60             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 4.37/4.60               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 4.37/4.60  thf('12', plain,
% 4.37/4.60      (![X27 : $i, X28 : $i]:
% 4.37/4.60         (~ (v1_relat_1 @ X27)
% 4.37/4.60          | (r1_tarski @ (k2_relat_1 @ X28) @ (k2_relat_1 @ X27))
% 4.37/4.60          | ~ (r1_tarski @ X28 @ X27)
% 4.37/4.60          | ~ (v1_relat_1 @ X28))),
% 4.37/4.60      inference('cnf', [status(esa)], [t25_relat_1])).
% 4.37/4.60  thf('13', plain,
% 4.37/4.60      ((~ (v1_relat_1 @ sk_A)
% 4.37/4.60        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 4.37/4.60        | ~ (v1_relat_1 @ sk_B))),
% 4.37/4.60      inference('sup-', [status(thm)], ['11', '12'])).
% 4.37/4.60  thf('14', plain, ((v1_relat_1 @ sk_A)),
% 4.37/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.60  thf('15', plain, ((v1_relat_1 @ sk_B)),
% 4.37/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.60  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 4.37/4.60      inference('demod', [status(thm)], ['13', '14', '15'])).
% 4.37/4.60  thf(t1_xboole_1, axiom,
% 4.37/4.60    (![A:$i,B:$i,C:$i]:
% 4.37/4.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 4.37/4.60       ( r1_tarski @ A @ C ) ))).
% 4.37/4.60  thf('17', plain,
% 4.37/4.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.37/4.60         (~ (r1_tarski @ X4 @ X5)
% 4.37/4.60          | ~ (r1_tarski @ X5 @ X6)
% 4.37/4.60          | (r1_tarski @ X4 @ X6))),
% 4.37/4.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 4.37/4.60  thf('18', plain,
% 4.37/4.60      (![X0 : $i]:
% 4.37/4.60         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 4.37/4.60          | ~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 4.37/4.60      inference('sup-', [status(thm)], ['16', '17'])).
% 4.37/4.60  thf('19', plain,
% 4.37/4.60      ((~ (v1_relat_1 @ sk_B)
% 4.37/4.60        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 4.37/4.60      inference('sup-', [status(thm)], ['10', '18'])).
% 4.37/4.60  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 4.37/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.60  thf('21', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.37/4.60      inference('demod', [status(thm)], ['19', '20'])).
% 4.37/4.60  thf('22', plain,
% 4.37/4.60      (![X26 : $i]:
% 4.37/4.60         (((k3_relat_1 @ X26)
% 4.37/4.60            = (k2_xboole_0 @ (k1_relat_1 @ X26) @ (k2_relat_1 @ X26)))
% 4.37/4.60          | ~ (v1_relat_1 @ X26))),
% 4.37/4.60      inference('cnf', [status(esa)], [d6_relat_1])).
% 4.37/4.60  thf(t7_xboole_1, axiom,
% 4.37/4.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 4.37/4.60  thf('23', plain,
% 4.37/4.60      (![X7 : $i, X8 : $i]: (r1_tarski @ X7 @ (k2_xboole_0 @ X7 @ X8))),
% 4.37/4.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 4.37/4.60  thf('24', plain,
% 4.37/4.60      (![X0 : $i]:
% 4.37/4.60         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 4.37/4.60          | ~ (v1_relat_1 @ X0))),
% 4.37/4.60      inference('sup+', [status(thm)], ['22', '23'])).
% 4.37/4.60  thf('25', plain, ((r1_tarski @ sk_A @ sk_B)),
% 4.37/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.60  thf('26', plain,
% 4.37/4.60      (![X27 : $i, X28 : $i]:
% 4.37/4.60         (~ (v1_relat_1 @ X27)
% 4.37/4.60          | (r1_tarski @ (k1_relat_1 @ X28) @ (k1_relat_1 @ X27))
% 4.37/4.60          | ~ (r1_tarski @ X28 @ X27)
% 4.37/4.60          | ~ (v1_relat_1 @ X28))),
% 4.37/4.60      inference('cnf', [status(esa)], [t25_relat_1])).
% 4.37/4.60  thf('27', plain,
% 4.37/4.60      ((~ (v1_relat_1 @ sk_A)
% 4.37/4.60        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 4.37/4.60        | ~ (v1_relat_1 @ sk_B))),
% 4.37/4.60      inference('sup-', [status(thm)], ['25', '26'])).
% 4.37/4.60  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 4.37/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.60  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 4.37/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.60  thf('30', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 4.37/4.60      inference('demod', [status(thm)], ['27', '28', '29'])).
% 4.37/4.60  thf('31', plain,
% 4.37/4.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.37/4.60         (~ (r1_tarski @ X4 @ X5)
% 4.37/4.60          | ~ (r1_tarski @ X5 @ X6)
% 4.37/4.60          | (r1_tarski @ X4 @ X6))),
% 4.37/4.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 4.37/4.60  thf('32', plain,
% 4.37/4.60      (![X0 : $i]:
% 4.37/4.60         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 4.37/4.60          | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 4.37/4.60      inference('sup-', [status(thm)], ['30', '31'])).
% 4.37/4.60  thf('33', plain,
% 4.37/4.60      ((~ (v1_relat_1 @ sk_B)
% 4.37/4.60        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 4.37/4.60      inference('sup-', [status(thm)], ['24', '32'])).
% 4.37/4.60  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 4.37/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.60  thf('35', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.37/4.60      inference('demod', [status(thm)], ['33', '34'])).
% 4.37/4.60  thf(t8_xboole_1, axiom,
% 4.37/4.60    (![A:$i,B:$i,C:$i]:
% 4.37/4.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 4.37/4.60       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 4.37/4.60  thf('36', plain,
% 4.37/4.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.37/4.60         (~ (r1_tarski @ X9 @ X10)
% 4.37/4.60          | ~ (r1_tarski @ X11 @ X10)
% 4.37/4.60          | (r1_tarski @ (k2_xboole_0 @ X9 @ X11) @ X10))),
% 4.37/4.60      inference('cnf', [status(esa)], [t8_xboole_1])).
% 4.37/4.60  thf('37', plain,
% 4.37/4.60      (![X0 : $i]:
% 4.37/4.60         ((r1_tarski @ (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ X0) @ 
% 4.37/4.60           (k3_relat_1 @ sk_B))
% 4.37/4.60          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 4.37/4.60      inference('sup-', [status(thm)], ['35', '36'])).
% 4.37/4.60  thf('38', plain,
% 4.37/4.60      ((r1_tarski @ 
% 4.37/4.60        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 4.37/4.60        (k3_relat_1 @ sk_B))),
% 4.37/4.60      inference('sup-', [status(thm)], ['21', '37'])).
% 4.37/4.60  thf('39', plain,
% 4.37/4.60      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 4.37/4.60        | ~ (v1_relat_1 @ sk_A))),
% 4.37/4.60      inference('sup+', [status(thm)], ['1', '38'])).
% 4.37/4.60  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 4.37/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.37/4.60  thf('41', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 4.37/4.60      inference('demod', [status(thm)], ['39', '40'])).
% 4.37/4.60  thf('42', plain, ($false), inference('demod', [status(thm)], ['0', '41'])).
% 4.37/4.60  
% 4.37/4.60  % SZS output end Refutation
% 4.37/4.60  
% 4.37/4.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
