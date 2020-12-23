%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LWdm8SdLkH

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:26 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 166 expanded)
%              Number of leaves         :   19 (  50 expanded)
%              Depth                    :   16
%              Number of atoms          :  434 (1350 expanded)
%              Number of equality atoms :   46 ( 151 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t38_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
      <=> ( B
          = ( k1_subset_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) )
        <=> ( B
            = ( k1_subset_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_subset_1])).

thf('1',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('5',plain,(
    ! [X23: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( ( k4_xboole_0 @ X10 @ X11 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X32: $i] :
      ( ( k1_subset_1 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('10',plain,
    ( ( sk_B_1
      = ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('11',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
   <= ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('13',plain,
    ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( sk_B_1 = k1_xboole_0 )
   <= ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('15',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ~ ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      & ( sk_B_1
        = ( k1_subset_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1
      = ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['1'])).

thf('18',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference('sat_resolution*',[status(thm)],['4','16','17'])).

thf('19',plain,(
    r1_tarski @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['2','18'])).

thf('20',plain,(
    ! [X10: $i,X12: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X12 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('21',plain,
    ( ( k4_xboole_0 @ sk_B_1 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i] :
      ( ( X6 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X32: $i] :
      ( ( k1_subset_1 @ X32 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('28',plain,
    ( ( sk_B_1
     != ( k1_subset_1 @ sk_A ) )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['3'])).

thf('29',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1
     != ( k1_subset_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_B_1
 != ( k1_subset_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['4','16'])).

thf('31',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_B @ sk_B_1 ) @ k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','31'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('33',plain,(
    ! [X18: $i] :
      ( ( k4_xboole_0 @ X18 @ k1_xboole_0 )
      = X18 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('34',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    r2_hidden @ ( sk_B @ sk_B_1 ) @ ( k3_subset_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['32','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k3_subset_1 @ X33 @ X34 )
        = ( k4_xboole_0 @ X33 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('41',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B_1 )
    = ( k4_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k3_subset_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r2_hidden @ ( sk_B @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['38','43'])).

thf('45',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','30'])).

thf('47',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LWdm8SdLkH
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:46:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 631 iterations in 0.246s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.46/0.70  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.46/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.70  thf(t7_xboole_0, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.46/0.70          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.46/0.70  thf('0', plain,
% 0.46/0.70      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.70  thf(t38_subset_1, conjecture,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.70       ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.46/0.70         ( ( B ) = ( k1_subset_1 @ A ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i,B:$i]:
% 0.46/0.70        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.70          ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ B ) ) <=>
% 0.46/0.70            ( ( B ) = ( k1_subset_1 @ A ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t38_subset_1])).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      ((((sk_B_1) = (k1_subset_1 @ sk_A))
% 0.46/0.70        | (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.46/0.70         <= (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.46/0.70      inference('split', [status(esa)], ['1'])).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      ((((sk_B_1) != (k1_subset_1 @ sk_A))
% 0.46/0.70        | ~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('4', plain,
% 0.46/0.70      (~ (((sk_B_1) = (k1_subset_1 @ sk_A))) | 
% 0.46/0.70       ~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('split', [status(esa)], ['3'])).
% 0.46/0.70  thf(t4_boole, axiom,
% 0.46/0.70    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      (![X23 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X23) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [t4_boole])).
% 0.46/0.70  thf(l32_xboole_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      (![X10 : $i, X11 : $i]:
% 0.46/0.70         ((r1_tarski @ X10 @ X11)
% 0.46/0.70          | ((k4_xboole_0 @ X10 @ X11) != (k1_xboole_0)))),
% 0.46/0.70      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.70  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.70      inference('simplify', [status(thm)], ['7'])).
% 0.46/0.70  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.46/0.70  thf('9', plain, (![X32 : $i]: ((k1_subset_1 @ X32) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      ((((sk_B_1) = (k1_subset_1 @ sk_A)))
% 0.46/0.70         <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.70      inference('split', [status(esa)], ['1'])).
% 0.46/0.70  thf('11', plain,
% 0.46/0.70      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))
% 0.46/0.70         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))))),
% 0.46/0.70      inference('split', [status(esa)], ['3'])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      ((~ (r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.46/0.70         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.46/0.70             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      ((((sk_B_1) = (k1_xboole_0))) <= ((((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.70      inference('sup+', [status(thm)], ['9', '10'])).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      ((~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ sk_A @ k1_xboole_0)))
% 0.46/0.70         <= (~ ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) & 
% 0.46/0.70             (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '14'])).
% 0.46/0.70  thf('16', plain,
% 0.46/0.70      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.46/0.70       ~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['8', '15'])).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))) | 
% 0.46/0.70       (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.46/0.70      inference('split', [status(esa)], ['1'])).
% 0.46/0.70  thf('18', plain, (((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['4', '16', '17'])).
% 0.46/0.70  thf('19', plain, ((r1_tarski @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['2', '18'])).
% 0.46/0.70  thf('20', plain,
% 0.46/0.70      (![X10 : $i, X12 : $i]:
% 0.46/0.70         (((k4_xboole_0 @ X10 @ X12) = (k1_xboole_0))
% 0.46/0.70          | ~ (r1_tarski @ X10 @ X12))),
% 0.46/0.70      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.46/0.70  thf('21', plain,
% 0.46/0.70      (((k4_xboole_0 @ sk_B_1 @ (k3_subset_1 @ sk_A @ sk_B_1)) = (k1_xboole_0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      (![X6 : $i]: (((X6) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X6) @ X6))),
% 0.46/0.70      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.46/0.70  thf(d5_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.46/0.70       ( ![D:$i]:
% 0.46/0.70         ( ( r2_hidden @ D @ C ) <=>
% 0.46/0.70           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.46/0.70          | (r2_hidden @ X0 @ X2)
% 0.46/0.70          | (r2_hidden @ X0 @ X3)
% 0.46/0.70          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.70      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.70         ((r2_hidden @ X0 @ (k4_xboole_0 @ X1 @ X2))
% 0.46/0.70          | (r2_hidden @ X0 @ X2)
% 0.46/0.70          | ~ (r2_hidden @ X0 @ X1))),
% 0.46/0.70      inference('simplify', [status(thm)], ['23'])).
% 0.46/0.70  thf('25', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (((X0) = (k1_xboole_0))
% 0.46/0.70          | (r2_hidden @ (sk_B @ X0) @ X1)
% 0.46/0.70          | (r2_hidden @ (sk_B @ X0) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['22', '24'])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)
% 0.46/0.70        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.46/0.70        | ((sk_B_1) = (k1_xboole_0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['21', '25'])).
% 0.46/0.70  thf('27', plain, (![X32 : $i]: ((k1_subset_1 @ X32) = (k1_xboole_0))),
% 0.46/0.70      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      ((((sk_B_1) != (k1_subset_1 @ sk_A)))
% 0.46/0.70         <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.70      inference('split', [status(esa)], ['3'])).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_subset_1 @ sk_A))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.46/0.70  thf('30', plain, (~ (((sk_B_1) = (k1_subset_1 @ sk_A)))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['4', '16'])).
% 0.46/0.70  thf('31', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      (((r2_hidden @ (sk_B @ sk_B_1) @ k1_xboole_0)
% 0.46/0.70        | (r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1)))),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['26', '31'])).
% 0.46/0.70  thf(t3_boole, axiom,
% 0.46/0.70    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.46/0.70  thf('33', plain, (![X18 : $i]: ((k4_xboole_0 @ X18 @ k1_xboole_0) = (X18))),
% 0.46/0.70      inference('cnf', [status(esa)], [t3_boole])).
% 0.46/0.70  thf('34', plain,
% 0.46/0.70      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X4 @ X3)
% 0.46/0.70          | ~ (r2_hidden @ X4 @ X2)
% 0.46/0.70          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.70      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X4 @ X2)
% 0.46/0.70          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.70  thf('36', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['33', '35'])).
% 0.46/0.70  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.46/0.70      inference('condensation', [status(thm)], ['36'])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      ((r2_hidden @ (sk_B @ sk_B_1) @ (k3_subset_1 @ sk_A @ sk_B_1))),
% 0.46/0.70      inference('clc', [status(thm)], ['32', '37'])).
% 0.46/0.70  thf('39', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(d5_subset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.70       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.46/0.70  thf('40', plain,
% 0.46/0.70      (![X33 : $i, X34 : $i]:
% 0.46/0.70         (((k3_subset_1 @ X33 @ X34) = (k4_xboole_0 @ X33 @ X34))
% 0.46/0.70          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X33)))),
% 0.46/0.70      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.46/0.70  thf('41', plain,
% 0.46/0.70      (((k3_subset_1 @ sk_A @ sk_B_1) = (k4_xboole_0 @ sk_A @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X4 @ X2)
% 0.46/0.70          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.46/0.70      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (r2_hidden @ X0 @ (k3_subset_1 @ sk_A @ sk_B_1))
% 0.46/0.70          | ~ (r2_hidden @ X0 @ sk_B_1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.70  thf('44', plain, (~ (r2_hidden @ (sk_B @ sk_B_1) @ sk_B_1)),
% 0.46/0.70      inference('sup-', [status(thm)], ['38', '43'])).
% 0.46/0.70  thf('45', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['0', '44'])).
% 0.46/0.70  thf('46', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf('47', plain, ($false),
% 0.46/0.70      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.54/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
