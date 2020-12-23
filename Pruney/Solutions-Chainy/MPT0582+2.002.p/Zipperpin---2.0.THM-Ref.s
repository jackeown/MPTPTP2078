%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UcoG2SxocX

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  88 expanded)
%              Number of leaves         :   17 (  32 expanded)
%              Depth                    :   14
%              Number of atoms          :  489 ( 928 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(t186_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
              & ( r1_tarski @ C @ B ) )
           => ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ! [C: $i] :
            ( ( v1_relat_1 @ C )
           => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
                & ( r1_tarski @ C @ B ) )
             => ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t186_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_C_2 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X11 ) @ ( sk_D_1 @ X10 @ X11 ) ) @ X11 )
      | ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('2',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ( ( k7_relat_1 @ X17 @ X18 )
        = X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( ( k7_relat_1 @ sk_C_2 @ sk_A )
      = sk_C_2 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( k7_relat_1 @ sk_C_2 @ sk_A )
    = sk_C_2 ),
    inference(demod,[status(thm)],['4','5'])).

thf(d11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k7_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ D @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X4
       != ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('8',plain,(
    ! [X5: $i,X6: $i,X7: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ X7 @ X6 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_C_2 @ sk_A ) )
      | ( r2_hidden @ X1 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( k7_relat_1 @ sk_C_2 @ sk_A )
    = sk_C_2 ),
    inference(demod,[status(thm)],['4','5'])).

thf('11',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_C_2 )
      | ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X11 ) @ ( sk_D_1 @ X10 @ X11 ) ) @ X11 )
      | ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('18',plain,(
    r1_tarski @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( sk_D_1 @ X0 @ sk_C_2 ) ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( sk_D_1 @ X0 @ sk_C_2 ) ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('25',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( X4
       != ( k7_relat_1 @ X5 @ X6 ) )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X5 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( r2_hidden @ X7 @ X6 )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X8 ) @ ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X2 ) @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( sk_D_1 @ X0 @ sk_C_2 ) ) @ ( k7_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( sk_D_1 @ X0 @ sk_C_2 ) ) @ ( k7_relat_1 @ sk_B @ X1 ) )
      | ~ ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C_2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( sk_D_1 @ X0 @ sk_C_2 ) ) @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X0 @ sk_C_2 ) @ ( sk_D_1 @ X0 @ sk_C_2 ) ) @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ sk_C_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X10 @ X11 ) @ ( sk_D_1 @ X10 @ X11 ) ) @ X10 )
      | ( r1_tarski @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('35',plain,
    ( ( r1_tarski @ sk_C_2 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ sk_C_2 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( r1_tarski @ sk_C_2 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( r1_tarski @ sk_C_2 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_C_2 @ ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference(demod,[status(thm)],['0','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UcoG2SxocX
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:27:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 48 iterations in 0.017s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.47  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.22/0.47  thf(t186_relat_1, conjecture,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ![C:$i]:
% 0.22/0.47         ( ( v1_relat_1 @ C ) =>
% 0.22/0.47           ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.22/0.47             ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i]:
% 0.22/0.47        ( ( v1_relat_1 @ B ) =>
% 0.22/0.47          ( ![C:$i]:
% 0.22/0.47            ( ( v1_relat_1 @ C ) =>
% 0.22/0.47              ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.22/0.47                  ( r1_tarski @ C @ B ) ) =>
% 0.22/0.47                ( r1_tarski @ C @ ( k7_relat_1 @ B @ A ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t186_relat_1])).
% 0.22/0.47  thf('0', plain, (~ (r1_tarski @ sk_C_2 @ (k7_relat_1 @ sk_B @ sk_A))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(d3_relat_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ![B:$i]:
% 0.22/0.47         ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.47           ( ![C:$i,D:$i]:
% 0.22/0.47             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.22/0.47               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      (![X10 : $i, X11 : $i]:
% 0.22/0.47         ((r2_hidden @ 
% 0.22/0.47           (k4_tarski @ (sk_C_1 @ X10 @ X11) @ (sk_D_1 @ X10 @ X11)) @ X11)
% 0.22/0.47          | (r1_tarski @ X11 @ X10)
% 0.22/0.47          | ~ (v1_relat_1 @ X11))),
% 0.22/0.47      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.47  thf('2', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(t97_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ B ) =>
% 0.22/0.47       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.22/0.47         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X17 : $i, X18 : $i]:
% 0.22/0.47         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.22/0.47          | ((k7_relat_1 @ X17 @ X18) = (X17))
% 0.22/0.47          | ~ (v1_relat_1 @ X17))),
% 0.22/0.47      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      ((~ (v1_relat_1 @ sk_C_2) | ((k7_relat_1 @ sk_C_2 @ sk_A) = (sk_C_2)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.47  thf('5', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('6', plain, (((k7_relat_1 @ sk_C_2 @ sk_A) = (sk_C_2))),
% 0.22/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf(d11_relat_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ![B:$i,C:$i]:
% 0.22/0.47         ( ( v1_relat_1 @ C ) =>
% 0.22/0.47           ( ( ( C ) = ( k7_relat_1 @ A @ B ) ) <=>
% 0.22/0.47             ( ![D:$i,E:$i]:
% 0.22/0.47               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.22/0.47                 ( ( r2_hidden @ D @ B ) & 
% 0.22/0.47                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X4)
% 0.22/0.47          | ((X4) != (k7_relat_1 @ X5 @ X6))
% 0.22/0.47          | (r2_hidden @ X7 @ X6)
% 0.22/0.47          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ X4)
% 0.22/0.47          | ~ (v1_relat_1 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X5 : $i, X6 : $i, X7 : $i, X9 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X5)
% 0.22/0.47          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (k7_relat_1 @ X5 @ X6))
% 0.22/0.47          | (r2_hidden @ X7 @ X6)
% 0.22/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_2)
% 0.22/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_C_2 @ sk_A))
% 0.22/0.47          | (r2_hidden @ X1 @ sk_A)
% 0.22/0.47          | ~ (v1_relat_1 @ sk_C_2))),
% 0.22/0.47      inference('sup-', [status(thm)], ['6', '8'])).
% 0.22/0.47  thf('10', plain, (((k7_relat_1 @ sk_C_2 @ sk_A) = (sk_C_2))),
% 0.22/0.47      inference('demod', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf('11', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('12', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('13', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ sk_C_2)
% 0.22/0.47          | (r2_hidden @ X1 @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ sk_C_2)
% 0.22/0.47          | (r1_tarski @ sk_C_2 @ X0)
% 0.22/0.47          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '13'])).
% 0.22/0.47  thf('15', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((r1_tarski @ sk_C_2 @ X0)
% 0.22/0.47          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (![X10 : $i, X11 : $i]:
% 0.22/0.47         ((r2_hidden @ 
% 0.22/0.47           (k4_tarski @ (sk_C_1 @ X10 @ X11) @ (sk_D_1 @ X10 @ X11)) @ X11)
% 0.22/0.47          | (r1_tarski @ X11 @ X10)
% 0.22/0.47          | ~ (v1_relat_1 @ X11))),
% 0.22/0.47      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.47  thf('18', plain, ((r1_tarski @ sk_C_2 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(d3_tarski, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.47       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.47          | (r2_hidden @ X0 @ X2)
% 0.22/0.47          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.47      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.47  thf('20', plain,
% 0.22/0.47      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C_2))),
% 0.22/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.47  thf('21', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ sk_C_2)
% 0.22/0.47          | (r1_tarski @ sk_C_2 @ X0)
% 0.22/0.47          | (r2_hidden @ 
% 0.22/0.47             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ (sk_D_1 @ X0 @ sk_C_2)) @ 
% 0.22/0.47             sk_B))),
% 0.22/0.47      inference('sup-', [status(thm)], ['17', '20'])).
% 0.22/0.47  thf('22', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('23', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((r1_tarski @ sk_C_2 @ X0)
% 0.22/0.47          | (r2_hidden @ 
% 0.22/0.47             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ (sk_D_1 @ X0 @ sk_C_2)) @ 
% 0.22/0.47             sk_B))),
% 0.22/0.47      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.47  thf(dt_k7_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.22/0.47  thf('24', plain,
% 0.22/0.47      (![X15 : $i, X16 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X15) | (v1_relat_1 @ (k7_relat_1 @ X15 @ X16)))),
% 0.22/0.47      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.22/0.47  thf('25', plain,
% 0.22/0.47      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X4)
% 0.22/0.47          | ((X4) != (k7_relat_1 @ X5 @ X6))
% 0.22/0.47          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ X4)
% 0.22/0.47          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X5)
% 0.22/0.47          | ~ (r2_hidden @ X7 @ X6)
% 0.22/0.47          | ~ (v1_relat_1 @ X5))),
% 0.22/0.47      inference('cnf', [status(esa)], [d11_relat_1])).
% 0.22/0.47  thf('26', plain,
% 0.22/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X5)
% 0.22/0.47          | ~ (r2_hidden @ X7 @ X6)
% 0.22/0.47          | ~ (r2_hidden @ (k4_tarski @ X7 @ X8) @ X5)
% 0.22/0.47          | (r2_hidden @ (k4_tarski @ X7 @ X8) @ (k7_relat_1 @ X5 @ X6))
% 0.22/0.47          | ~ (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.22/0.47      inference('simplify', [status(thm)], ['25'])).
% 0.22/0.47  thf('27', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.47         (~ (v1_relat_1 @ X1)
% 0.22/0.47          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.47          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.22/0.47          | ~ (r2_hidden @ X3 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ X1))),
% 0.22/0.47      inference('sup-', [status(thm)], ['24', '26'])).
% 0.22/0.47  thf('28', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X3 @ X0)
% 0.22/0.47          | ~ (r2_hidden @ (k4_tarski @ X3 @ X2) @ X1)
% 0.22/0.47          | (r2_hidden @ (k4_tarski @ X3 @ X2) @ (k7_relat_1 @ X1 @ X0))
% 0.22/0.47          | ~ (v1_relat_1 @ X1))),
% 0.22/0.47      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.47  thf('29', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((r1_tarski @ sk_C_2 @ X0)
% 0.22/0.47          | ~ (v1_relat_1 @ sk_B)
% 0.22/0.47          | (r2_hidden @ 
% 0.22/0.47             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ (sk_D_1 @ X0 @ sk_C_2)) @ 
% 0.22/0.47             (k7_relat_1 @ sk_B @ X1))
% 0.22/0.47          | ~ (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X1))),
% 0.22/0.47      inference('sup-', [status(thm)], ['23', '28'])).
% 0.22/0.47  thf('30', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('31', plain,
% 0.22/0.47      (![X0 : $i, X1 : $i]:
% 0.22/0.47         ((r1_tarski @ sk_C_2 @ X0)
% 0.22/0.47          | (r2_hidden @ 
% 0.22/0.47             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ (sk_D_1 @ X0 @ sk_C_2)) @ 
% 0.22/0.47             (k7_relat_1 @ sk_B @ X1))
% 0.22/0.47          | ~ (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X1))),
% 0.22/0.47      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.47  thf('32', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((r1_tarski @ sk_C_2 @ X0)
% 0.22/0.47          | (r2_hidden @ 
% 0.22/0.47             (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ (sk_D_1 @ X0 @ sk_C_2)) @ 
% 0.22/0.47             (k7_relat_1 @ sk_B @ sk_A))
% 0.22/0.47          | (r1_tarski @ sk_C_2 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['16', '31'])).
% 0.22/0.47  thf('33', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((r2_hidden @ 
% 0.22/0.47           (k4_tarski @ (sk_C_1 @ X0 @ sk_C_2) @ (sk_D_1 @ X0 @ sk_C_2)) @ 
% 0.22/0.47           (k7_relat_1 @ sk_B @ sk_A))
% 0.22/0.47          | (r1_tarski @ sk_C_2 @ X0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['32'])).
% 0.22/0.47  thf('34', plain,
% 0.22/0.47      (![X10 : $i, X11 : $i]:
% 0.22/0.47         (~ (r2_hidden @ 
% 0.22/0.47             (k4_tarski @ (sk_C_1 @ X10 @ X11) @ (sk_D_1 @ X10 @ X11)) @ X10)
% 0.22/0.47          | (r1_tarski @ X11 @ X10)
% 0.22/0.47          | ~ (v1_relat_1 @ X11))),
% 0.22/0.47      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.22/0.47  thf('35', plain,
% 0.22/0.47      (((r1_tarski @ sk_C_2 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.22/0.47        | ~ (v1_relat_1 @ sk_C_2)
% 0.22/0.47        | (r1_tarski @ sk_C_2 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.47  thf('36', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('37', plain,
% 0.22/0.47      (((r1_tarski @ sk_C_2 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.22/0.47        | (r1_tarski @ sk_C_2 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.22/0.47      inference('demod', [status(thm)], ['35', '36'])).
% 0.22/0.47  thf('38', plain, ((r1_tarski @ sk_C_2 @ (k7_relat_1 @ sk_B @ sk_A))),
% 0.22/0.47      inference('simplify', [status(thm)], ['37'])).
% 0.22/0.47  thf('39', plain, ($false), inference('demod', [status(thm)], ['0', '38'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
