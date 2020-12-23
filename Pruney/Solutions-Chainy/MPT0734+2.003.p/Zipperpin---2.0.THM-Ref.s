%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QFi867vuAJ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:46 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 144 expanded)
%              Number of leaves         :   18 (  49 expanded)
%              Depth                    :   18
%              Number of atoms          :  306 (1180 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r3_xboole_0_type,type,(
    r3_xboole_0: $i > $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_ordinal1_type,type,(
    v2_ordinal1: $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(t22_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ! [C: $i] :
              ( ( v3_ordinal1 @ C )
             => ( ( ( r1_tarski @ A @ B )
                  & ( r2_hidden @ B @ C ) )
               => ( r2_hidden @ A @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_ordinal1 @ A )
       => ! [B: $i] :
            ( ( v3_ordinal1 @ B )
           => ! [C: $i] :
                ( ( v3_ordinal1 @ C )
               => ( ( ( r1_tarski @ A @ B )
                    & ( r2_hidden @ B @ C ) )
                 => ( r2_hidden @ A @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_ordinal1])).

thf('0',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(antisymmetry_r2_hidden,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[antisymmetry_r2_hidden])).

thf('2',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(cc1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( ( v1_ordinal1 @ A )
        & ( v2_ordinal1 @ A ) ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( v1_ordinal1 @ X11 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('4',plain,(
    ! [X11: $i] :
      ( ( v1_ordinal1 @ X11 )
      | ~ ( v3_ordinal1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_ordinal1])).

thf('5',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ B @ A )
         => ( r1_tarski @ B @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ( r1_tarski @ X12 @ X13 )
      | ~ ( v1_ordinal1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('7',plain,
    ( ~ ( v1_ordinal1 @ sk_C )
    | ( r1_tarski @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( v3_ordinal1 @ sk_C )
    | ( r1_tarski @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9'])).

thf(d9_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r3_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        | ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r3_xboole_0 @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_xboole_0])).

thf('12',plain,(
    r3_xboole_0 @ sk_B_1 @ sk_C ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t104_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ~ ( r2_xboole_0 @ A @ B )
          & ( A != B )
          & ~ ( r2_xboole_0 @ B @ A ) )
    <=> ( r3_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r2_xboole_0 @ X7 @ X5 )
      | ( X5 = X7 )
      | ( r2_xboole_0 @ X5 @ X7 )
      | ~ ( r3_xboole_0 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t104_xboole_1])).

thf('14',plain,
    ( ( r2_xboole_0 @ sk_B_1 @ sk_C )
    | ( sk_B_1 = sk_C )
    | ( r2_xboole_0 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t21_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
     => ! [B: $i] :
          ( ( v3_ordinal1 @ B )
         => ( ( r2_xboole_0 @ A @ B )
           => ( r2_hidden @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_xboole_0 @ X16 @ X15 )
      | ~ ( v1_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('16',plain,
    ( ( sk_B_1 = sk_C )
    | ( r2_xboole_0 @ sk_B_1 @ sk_C )
    | ~ ( v1_ordinal1 @ sk_C )
    | ( r2_hidden @ sk_C @ sk_B_1 )
    | ~ ( v3_ordinal1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v3_ordinal1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( sk_B_1 = sk_C )
    | ( r2_xboole_0 @ sk_B_1 @ sk_C )
    | ~ ( v1_ordinal1 @ sk_C )
    | ( r2_hidden @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v3_ordinal1 @ sk_C )
    | ( r2_hidden @ sk_C @ sk_B_1 )
    | ( r2_xboole_0 @ sk_B_1 @ sk_C )
    | ( sk_B_1 = sk_C ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( r2_hidden @ sk_C @ sk_B_1 )
    | ( r2_xboole_0 @ sk_B_1 @ sk_C )
    | ( sk_B_1 = sk_C ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( r2_hidden @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('23',plain,
    ( ( sk_B_1 = sk_C )
    | ( r2_xboole_0 @ sk_B_1 @ sk_C ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t59_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r2_xboole_0 @ B @ C ) )
     => ( r2_xboole_0 @ A @ C ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r2_xboole_0 @ X9 @ X10 )
      | ( r2_xboole_0 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t59_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_xboole_0 @ sk_A @ X0 )
      | ~ ( r2_xboole_0 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_B_1 = sk_C )
    | ( r2_xboole_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v3_ordinal1 @ X15 )
      | ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_xboole_0 @ X16 @ X15 )
      | ~ ( v1_ordinal1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t21_ordinal1])).

thf('29',plain,
    ( ( sk_B_1 = sk_C )
    | ~ ( v1_ordinal1 @ sk_A )
    | ( r2_hidden @ sk_A @ sk_C )
    | ~ ( v3_ordinal1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v3_ordinal1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B_1 = sk_C )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    sk_B_1 = sk_C ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,(
    ~ ( r2_hidden @ sk_B_1 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','34'])).

thf('36',plain,(
    r2_hidden @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B_1 = sk_C ),
    inference(clc,[status(thm)],['32','33'])).

thf('38',plain,(
    r2_hidden @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['35','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QFi867vuAJ
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.45  % Solved by: fo/fo7.sh
% 0.19/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.45  % done 56 iterations in 0.024s
% 0.19/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.45  % SZS output start Refutation
% 0.19/0.45  thf(r3_xboole_0_type, type, r3_xboole_0: $i > $i > $o).
% 0.19/0.45  thf(v3_ordinal1_type, type, v3_ordinal1: $i > $o).
% 0.19/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.45  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.19/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.45  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.19/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.45  thf(v2_ordinal1_type, type, v2_ordinal1: $i > $o).
% 0.19/0.45  thf(v1_ordinal1_type, type, v1_ordinal1: $i > $o).
% 0.19/0.45  thf(t22_ordinal1, conjecture,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v1_ordinal1 @ A ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( v3_ordinal1 @ B ) =>
% 0.19/0.45           ( ![C:$i]:
% 0.19/0.45             ( ( v3_ordinal1 @ C ) =>
% 0.19/0.45               ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.19/0.45                 ( r2_hidden @ A @ C ) ) ) ) ) ) ))).
% 0.19/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.45    (~( ![A:$i]:
% 0.19/0.45        ( ( v1_ordinal1 @ A ) =>
% 0.19/0.45          ( ![B:$i]:
% 0.19/0.45            ( ( v3_ordinal1 @ B ) =>
% 0.19/0.45              ( ![C:$i]:
% 0.19/0.45                ( ( v3_ordinal1 @ C ) =>
% 0.19/0.45                  ( ( ( r1_tarski @ A @ B ) & ( r2_hidden @ B @ C ) ) =>
% 0.19/0.45                    ( r2_hidden @ A @ C ) ) ) ) ) ) ) )),
% 0.19/0.45    inference('cnf.neg', [status(esa)], [t22_ordinal1])).
% 0.19/0.45  thf('0', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(antisymmetry_r2_hidden, axiom,
% 0.19/0.45    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( ~( r2_hidden @ B @ A ) ) ))).
% 0.19/0.45  thf('1', plain,
% 0.19/0.45      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (r2_hidden @ X1 @ X0))),
% 0.19/0.45      inference('cnf', [status(esa)], [antisymmetry_r2_hidden])).
% 0.19/0.45  thf('2', plain, (~ (r2_hidden @ sk_C @ sk_B_1)),
% 0.19/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.45  thf(cc1_ordinal1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v3_ordinal1 @ A ) => ( ( v1_ordinal1 @ A ) & ( v2_ordinal1 @ A ) ) ))).
% 0.19/0.45  thf('3', plain, (![X11 : $i]: ((v1_ordinal1 @ X11) | ~ (v3_ordinal1 @ X11))),
% 0.19/0.45      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.19/0.45  thf('4', plain, (![X11 : $i]: ((v1_ordinal1 @ X11) | ~ (v3_ordinal1 @ X11))),
% 0.19/0.45      inference('cnf', [status(esa)], [cc1_ordinal1])).
% 0.19/0.45  thf('5', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(d2_ordinal1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v1_ordinal1 @ A ) <=>
% 0.19/0.45       ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( r1_tarski @ B @ A ) ) ) ))).
% 0.19/0.45  thf('6', plain,
% 0.19/0.45      (![X12 : $i, X13 : $i]:
% 0.19/0.45         (~ (r2_hidden @ X12 @ X13)
% 0.19/0.45          | (r1_tarski @ X12 @ X13)
% 0.19/0.45          | ~ (v1_ordinal1 @ X13))),
% 0.19/0.45      inference('cnf', [status(esa)], [d2_ordinal1])).
% 0.19/0.45  thf('7', plain, ((~ (v1_ordinal1 @ sk_C) | (r1_tarski @ sk_B_1 @ sk_C))),
% 0.19/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.45  thf('8', plain, ((~ (v3_ordinal1 @ sk_C) | (r1_tarski @ sk_B_1 @ sk_C))),
% 0.19/0.45      inference('sup-', [status(thm)], ['4', '7'])).
% 0.19/0.45  thf('9', plain, ((v3_ordinal1 @ sk_C)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('10', plain, ((r1_tarski @ sk_B_1 @ sk_C)),
% 0.19/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.19/0.45  thf(d9_xboole_0, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( r3_xboole_0 @ A @ B ) <=>
% 0.19/0.45       ( ( r1_tarski @ A @ B ) | ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.45  thf('11', plain,
% 0.19/0.45      (![X3 : $i, X4 : $i]: ((r3_xboole_0 @ X3 @ X4) | ~ (r1_tarski @ X3 @ X4))),
% 0.19/0.45      inference('cnf', [status(esa)], [d9_xboole_0])).
% 0.19/0.45  thf('12', plain, ((r3_xboole_0 @ sk_B_1 @ sk_C)),
% 0.19/0.45      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.45  thf(t104_xboole_1, axiom,
% 0.19/0.45    (![A:$i,B:$i]:
% 0.19/0.45     ( ( ~( ( ~( r2_xboole_0 @ A @ B ) ) & ( ( A ) != ( B ) ) & 
% 0.19/0.45            ( ~( r2_xboole_0 @ B @ A ) ) ) ) <=>
% 0.19/0.45       ( r3_xboole_0 @ A @ B ) ))).
% 0.19/0.45  thf('13', plain,
% 0.19/0.45      (![X5 : $i, X7 : $i]:
% 0.19/0.45         ((r2_xboole_0 @ X7 @ X5)
% 0.19/0.45          | ((X5) = (X7))
% 0.19/0.45          | (r2_xboole_0 @ X5 @ X7)
% 0.19/0.45          | ~ (r3_xboole_0 @ X5 @ X7))),
% 0.19/0.45      inference('cnf', [status(esa)], [t104_xboole_1])).
% 0.19/0.45  thf('14', plain,
% 0.19/0.45      (((r2_xboole_0 @ sk_B_1 @ sk_C)
% 0.19/0.45        | ((sk_B_1) = (sk_C))
% 0.19/0.45        | (r2_xboole_0 @ sk_C @ sk_B_1))),
% 0.19/0.45      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.45  thf(t21_ordinal1, axiom,
% 0.19/0.45    (![A:$i]:
% 0.19/0.45     ( ( v1_ordinal1 @ A ) =>
% 0.19/0.45       ( ![B:$i]:
% 0.19/0.45         ( ( v3_ordinal1 @ B ) =>
% 0.19/0.45           ( ( r2_xboole_0 @ A @ B ) => ( r2_hidden @ A @ B ) ) ) ) ))).
% 0.19/0.45  thf('15', plain,
% 0.19/0.45      (![X15 : $i, X16 : $i]:
% 0.19/0.45         (~ (v3_ordinal1 @ X15)
% 0.19/0.45          | (r2_hidden @ X16 @ X15)
% 0.19/0.45          | ~ (r2_xboole_0 @ X16 @ X15)
% 0.19/0.45          | ~ (v1_ordinal1 @ X16))),
% 0.19/0.45      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.19/0.45  thf('16', plain,
% 0.19/0.45      ((((sk_B_1) = (sk_C))
% 0.19/0.45        | (r2_xboole_0 @ sk_B_1 @ sk_C)
% 0.19/0.45        | ~ (v1_ordinal1 @ sk_C)
% 0.19/0.45        | (r2_hidden @ sk_C @ sk_B_1)
% 0.19/0.45        | ~ (v3_ordinal1 @ sk_B_1))),
% 0.19/0.45      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.45  thf('17', plain, ((v3_ordinal1 @ sk_B_1)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('18', plain,
% 0.19/0.45      ((((sk_B_1) = (sk_C))
% 0.19/0.45        | (r2_xboole_0 @ sk_B_1 @ sk_C)
% 0.19/0.45        | ~ (v1_ordinal1 @ sk_C)
% 0.19/0.45        | (r2_hidden @ sk_C @ sk_B_1))),
% 0.19/0.45      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.45  thf('19', plain,
% 0.19/0.45      ((~ (v3_ordinal1 @ sk_C)
% 0.19/0.45        | (r2_hidden @ sk_C @ sk_B_1)
% 0.19/0.45        | (r2_xboole_0 @ sk_B_1 @ sk_C)
% 0.19/0.45        | ((sk_B_1) = (sk_C)))),
% 0.19/0.45      inference('sup-', [status(thm)], ['3', '18'])).
% 0.19/0.45  thf('20', plain, ((v3_ordinal1 @ sk_C)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('21', plain,
% 0.19/0.45      (((r2_hidden @ sk_C @ sk_B_1)
% 0.19/0.45        | (r2_xboole_0 @ sk_B_1 @ sk_C)
% 0.19/0.45        | ((sk_B_1) = (sk_C)))),
% 0.19/0.45      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.45  thf('22', plain, (~ (r2_hidden @ sk_C @ sk_B_1)),
% 0.19/0.45      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.45  thf('23', plain, ((((sk_B_1) = (sk_C)) | (r2_xboole_0 @ sk_B_1 @ sk_C))),
% 0.19/0.45      inference('clc', [status(thm)], ['21', '22'])).
% 0.19/0.45  thf('24', plain, ((r1_tarski @ sk_A @ sk_B_1)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf(t59_xboole_1, axiom,
% 0.19/0.45    (![A:$i,B:$i,C:$i]:
% 0.19/0.45     ( ( ( r1_tarski @ A @ B ) & ( r2_xboole_0 @ B @ C ) ) =>
% 0.19/0.45       ( r2_xboole_0 @ A @ C ) ))).
% 0.19/0.45  thf('25', plain,
% 0.19/0.45      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.45         (~ (r1_tarski @ X8 @ X9)
% 0.19/0.45          | ~ (r2_xboole_0 @ X9 @ X10)
% 0.19/0.45          | (r2_xboole_0 @ X8 @ X10))),
% 0.19/0.45      inference('cnf', [status(esa)], [t59_xboole_1])).
% 0.19/0.45  thf('26', plain,
% 0.19/0.45      (![X0 : $i]: ((r2_xboole_0 @ sk_A @ X0) | ~ (r2_xboole_0 @ sk_B_1 @ X0))),
% 0.19/0.45      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.45  thf('27', plain, ((((sk_B_1) = (sk_C)) | (r2_xboole_0 @ sk_A @ sk_C))),
% 0.19/0.45      inference('sup-', [status(thm)], ['23', '26'])).
% 0.19/0.45  thf('28', plain,
% 0.19/0.45      (![X15 : $i, X16 : $i]:
% 0.19/0.45         (~ (v3_ordinal1 @ X15)
% 0.19/0.45          | (r2_hidden @ X16 @ X15)
% 0.19/0.45          | ~ (r2_xboole_0 @ X16 @ X15)
% 0.19/0.45          | ~ (v1_ordinal1 @ X16))),
% 0.19/0.45      inference('cnf', [status(esa)], [t21_ordinal1])).
% 0.19/0.45  thf('29', plain,
% 0.19/0.45      ((((sk_B_1) = (sk_C))
% 0.19/0.45        | ~ (v1_ordinal1 @ sk_A)
% 0.19/0.45        | (r2_hidden @ sk_A @ sk_C)
% 0.19/0.45        | ~ (v3_ordinal1 @ sk_C))),
% 0.19/0.45      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.45  thf('30', plain, ((v1_ordinal1 @ sk_A)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('31', plain, ((v3_ordinal1 @ sk_C)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('32', plain, ((((sk_B_1) = (sk_C)) | (r2_hidden @ sk_A @ sk_C))),
% 0.19/0.45      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.19/0.45  thf('33', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('34', plain, (((sk_B_1) = (sk_C))),
% 0.19/0.45      inference('clc', [status(thm)], ['32', '33'])).
% 0.19/0.45  thf('35', plain, (~ (r2_hidden @ sk_B_1 @ sk_B_1)),
% 0.19/0.45      inference('demod', [status(thm)], ['2', '34'])).
% 0.19/0.45  thf('36', plain, ((r2_hidden @ sk_B_1 @ sk_C)),
% 0.19/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.45  thf('37', plain, (((sk_B_1) = (sk_C))),
% 0.19/0.45      inference('clc', [status(thm)], ['32', '33'])).
% 0.19/0.45  thf('38', plain, ((r2_hidden @ sk_B_1 @ sk_B_1)),
% 0.19/0.45      inference('demod', [status(thm)], ['36', '37'])).
% 0.19/0.45  thf('39', plain, ($false), inference('demod', [status(thm)], ['35', '38'])).
% 0.19/0.45  
% 0.19/0.45  % SZS output end Refutation
% 0.19/0.45  
% 0.19/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
