%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YUvPH5MwDB

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:52 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :   54 (  87 expanded)
%              Number of leaves         :   15 (  31 expanded)
%              Depth                    :   13
%              Number of atoms          :  341 ( 596 expanded)
%              Number of equality atoms :   13 (  25 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t17_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_setfam_1 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ A @ B )
       => ( r1_setfam_1 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t17_setfam_1])).

thf('0',plain,(
    ~ ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_setfam_1 @ X26 @ X27 )
      | ( r2_hidden @ ( sk_C @ X27 @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( r2_hidden @ X2 @ X5 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X2 @ ( k4_xboole_0 @ X3 @ X4 ) )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_setfam_1 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k4_xboole_0 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ( X8 != X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['5'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X11 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('10',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_xboole_0 @ X15 @ X14 )
        = X14 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('11',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X11 @ X13 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_B @ X0 )
      | ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('15',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('18',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 )
      | ~ ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_A @ sk_B )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ X1 ) )
      | ( X0
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ X1 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['28'])).

thf('30',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B )
      | ( r1_setfam_1 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','30'])).

thf('32',plain,(
    ! [X9: $i] :
      ( r1_tarski @ X9 @ X9 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('33',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r1_setfam_1 @ X26 @ X27 )
      | ~ ( r2_hidden @ X28 @ X27 )
      | ~ ( r1_tarski @ ( sk_C @ X27 @ X26 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( r1_setfam_1 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r1_setfam_1 @ sk_A @ sk_B )
    | ( r1_setfam_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    r1_setfam_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YUvPH5MwDB
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:39:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.52/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.74  % Solved by: fo/fo7.sh
% 0.52/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.74  % done 859 iterations in 0.287s
% 0.52/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.74  % SZS output start Refutation
% 0.52/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.52/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.52/0.74  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.52/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.74  thf(t17_setfam_1, conjecture,
% 0.52/0.74    (![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ))).
% 0.52/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.74    (~( ![A:$i,B:$i]: ( ( r1_tarski @ A @ B ) => ( r1_setfam_1 @ A @ B ) ) )),
% 0.52/0.74    inference('cnf.neg', [status(esa)], [t17_setfam_1])).
% 0.52/0.74  thf('0', plain, (~ (r1_setfam_1 @ sk_A @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(d2_setfam_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.52/0.74       ( ![C:$i]:
% 0.52/0.74         ( ~( ( r2_hidden @ C @ A ) & 
% 0.52/0.74              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.52/0.74  thf('1', plain,
% 0.52/0.74      (![X26 : $i, X27 : $i]:
% 0.52/0.74         ((r1_setfam_1 @ X26 @ X27) | (r2_hidden @ (sk_C @ X27 @ X26) @ X26))),
% 0.52/0.74      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.52/0.74  thf(d5_xboole_0, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.52/0.74       ( ![D:$i]:
% 0.52/0.74         ( ( r2_hidden @ D @ C ) <=>
% 0.52/0.74           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.52/0.74  thf('2', plain,
% 0.52/0.74      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X2 @ X3)
% 0.52/0.74          | (r2_hidden @ X2 @ X4)
% 0.52/0.74          | (r2_hidden @ X2 @ X5)
% 0.52/0.74          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.74  thf('3', plain,
% 0.52/0.74      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.52/0.74         ((r2_hidden @ X2 @ (k4_xboole_0 @ X3 @ X4))
% 0.52/0.74          | (r2_hidden @ X2 @ X4)
% 0.52/0.74          | ~ (r2_hidden @ X2 @ X3))),
% 0.52/0.74      inference('simplify', [status(thm)], ['2'])).
% 0.52/0.74  thf('4', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         ((r1_setfam_1 @ X0 @ X1)
% 0.52/0.74          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2)
% 0.52/0.74          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k4_xboole_0 @ X0 @ X2)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['1', '3'])).
% 0.52/0.74  thf(d10_xboole_0, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.74  thf('5', plain,
% 0.52/0.74      (![X8 : $i, X9 : $i]: ((r1_tarski @ X8 @ X9) | ((X8) != (X9)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.74  thf('6', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.52/0.74      inference('simplify', [status(thm)], ['5'])).
% 0.52/0.74  thf(t11_xboole_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.52/0.74  thf('7', plain,
% 0.52/0.74      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.52/0.74         ((r1_tarski @ X11 @ X12)
% 0.52/0.74          | ~ (r1_tarski @ (k2_xboole_0 @ X11 @ X13) @ X12))),
% 0.52/0.74      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.52/0.74  thf('8', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.74  thf('9', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.52/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.74  thf(t12_xboole_1, axiom,
% 0.52/0.74    (![A:$i,B:$i]:
% 0.52/0.74     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.52/0.74  thf('10', plain,
% 0.52/0.74      (![X14 : $i, X15 : $i]:
% 0.52/0.74         (((k2_xboole_0 @ X15 @ X14) = (X14)) | ~ (r1_tarski @ X15 @ X14))),
% 0.52/0.74      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.52/0.74  thf('11', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.52/0.74      inference('sup-', [status(thm)], ['9', '10'])).
% 0.52/0.74  thf('12', plain,
% 0.52/0.74      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.52/0.74         ((r1_tarski @ X11 @ X12)
% 0.52/0.74          | ~ (r1_tarski @ (k2_xboole_0 @ X11 @ X13) @ X12))),
% 0.52/0.74      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.52/0.74  thf('13', plain,
% 0.52/0.74      (![X0 : $i]: (~ (r1_tarski @ sk_B @ X0) | (r1_tarski @ sk_A @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['11', '12'])).
% 0.52/0.74  thf('14', plain,
% 0.52/0.74      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['8', '13'])).
% 0.52/0.74  thf(t43_xboole_1, axiom,
% 0.52/0.74    (![A:$i,B:$i,C:$i]:
% 0.52/0.74     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.52/0.74       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.52/0.74  thf('15', plain,
% 0.52/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.74         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.52/0.74          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.52/0.74  thf('16', plain,
% 0.52/0.74      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.52/0.74      inference('sup-', [status(thm)], ['14', '15'])).
% 0.52/0.74  thf('17', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['6', '7'])).
% 0.52/0.74  thf('18', plain,
% 0.52/0.74      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.74         ((r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20)
% 0.52/0.74          | ~ (r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20)))),
% 0.52/0.74      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.52/0.74  thf('19', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.52/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.74  thf('20', plain,
% 0.52/0.74      (![X8 : $i, X10 : $i]:
% 0.52/0.74         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.52/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.74  thf('21', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X1))
% 0.52/0.74          | ((X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['19', '20'])).
% 0.52/0.74  thf('22', plain,
% 0.52/0.74      (![X0 : $i]: ((k4_xboole_0 @ sk_A @ sk_B) = (k4_xboole_0 @ X0 @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['16', '21'])).
% 0.52/0.74  thf('23', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.52/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.52/0.74  thf('24', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ X1))
% 0.52/0.74          | ((X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.52/0.74      inference('sup-', [status(thm)], ['19', '20'])).
% 0.52/0.74  thf('25', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: ((k4_xboole_0 @ X1 @ X1) = (k4_xboole_0 @ X0 @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.74  thf('26', plain,
% 0.52/0.74      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X6 @ X5)
% 0.52/0.74          | ~ (r2_hidden @ X6 @ X4)
% 0.52/0.74          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.52/0.74      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.52/0.74  thf('27', plain,
% 0.52/0.74      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X6 @ X4)
% 0.52/0.74          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.52/0.74      inference('simplify', [status(thm)], ['26'])).
% 0.52/0.74  thf('28', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.74         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X0 @ X0))
% 0.52/0.74          | ~ (r2_hidden @ X2 @ X1))),
% 0.52/0.74      inference('sup-', [status(thm)], ['25', '27'])).
% 0.52/0.74  thf('29', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ X0 @ X0))),
% 0.52/0.74      inference('condensation', [status(thm)], ['28'])).
% 0.52/0.74  thf('30', plain,
% 0.52/0.74      (![X1 : $i]: ~ (r2_hidden @ X1 @ (k4_xboole_0 @ sk_A @ sk_B))),
% 0.52/0.74      inference('sup-', [status(thm)], ['22', '29'])).
% 0.52/0.74  thf('31', plain,
% 0.52/0.74      (![X0 : $i]:
% 0.52/0.74         ((r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B) | (r1_setfam_1 @ sk_A @ X0))),
% 0.52/0.74      inference('sup-', [status(thm)], ['4', '30'])).
% 0.52/0.74  thf('32', plain, (![X9 : $i]: (r1_tarski @ X9 @ X9)),
% 0.52/0.74      inference('simplify', [status(thm)], ['5'])).
% 0.52/0.74  thf('33', plain,
% 0.52/0.74      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.52/0.74         ((r1_setfam_1 @ X26 @ X27)
% 0.52/0.74          | ~ (r2_hidden @ X28 @ X27)
% 0.52/0.74          | ~ (r1_tarski @ (sk_C @ X27 @ X26) @ X28))),
% 0.52/0.74      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.52/0.74  thf('34', plain,
% 0.52/0.74      (![X0 : $i, X1 : $i]:
% 0.52/0.74         (~ (r2_hidden @ (sk_C @ X1 @ X0) @ X1) | (r1_setfam_1 @ X0 @ X1))),
% 0.52/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.52/0.74  thf('35', plain,
% 0.52/0.74      (((r1_setfam_1 @ sk_A @ sk_B) | (r1_setfam_1 @ sk_A @ sk_B))),
% 0.52/0.74      inference('sup-', [status(thm)], ['31', '34'])).
% 0.52/0.74  thf('36', plain, ((r1_setfam_1 @ sk_A @ sk_B)),
% 0.52/0.74      inference('simplify', [status(thm)], ['35'])).
% 0.52/0.74  thf('37', plain, ($false), inference('demod', [status(thm)], ['0', '36'])).
% 0.52/0.74  
% 0.52/0.74  % SZS output end Refutation
% 0.52/0.74  
% 0.52/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
