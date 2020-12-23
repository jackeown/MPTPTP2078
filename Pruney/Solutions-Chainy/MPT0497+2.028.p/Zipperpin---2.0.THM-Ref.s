%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kSXsfgIPTz

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:09 EST 2020

% Result     : Theorem 0.34s
% Output     : Refutation 0.34s
% Verified   : 
% Statistics : Number of formulae       :   65 (  89 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  495 ( 739 expanded)
%              Number of equality atoms :   45 (  69 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i )).

thf(t95_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k7_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t95_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X42 @ X43 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X42 ) @ X43 ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X42 @ X43 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X42 ) @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( ( k1_relat_1 @ k1_xboole_0 )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('12',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X2 ) )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('17',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('21',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X42 @ X43 ) )
        = ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X42 ) @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('22',plain,(
    ! [X41: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X41 ) @ ( sk_C_1 @ X41 ) ) @ X41 )
      | ( X41 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('23',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X38 @ X39 ) @ X40 )
      | ( r2_hidden @ X38 @ ( k1_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_B @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_B @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( k1_setfam_1 @ ( k2_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('30',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X34 @ X35 ) )
      = ( k3_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('31',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k1_setfam_1 @ ( k2_tarski @ X3 @ X6 ) ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,
    ( ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B_1 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k7_relat_1 @ sk_B_1 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k7_relat_1 @ sk_B_1 @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B_1 ) @ sk_A )
    | ( ( k7_relat_1 @ sk_B_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','17','18','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kSXsfgIPTz
% 0.14/0.36  % Computer   : n024.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:47:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.34/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.34/0.53  % Solved by: fo/fo7.sh
% 0.34/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.34/0.53  % done 58 iterations in 0.048s
% 0.34/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.34/0.53  % SZS output start Refutation
% 0.34/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.34/0.53  thf(sk_B_type, type, sk_B: $i > $i).
% 0.34/0.53  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.34/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.34/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.34/0.53  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.34/0.53  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.34/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.34/0.53  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.34/0.53  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.34/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.34/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.34/0.53  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.34/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.34/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i).
% 0.34/0.53  thf(t95_relat_1, conjecture,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ B ) =>
% 0.34/0.53       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.34/0.53         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.34/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.34/0.53    (~( ![A:$i,B:$i]:
% 0.34/0.53        ( ( v1_relat_1 @ B ) =>
% 0.34/0.53          ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.34/0.53            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.34/0.53    inference('cnf.neg', [status(esa)], [t95_relat_1])).
% 0.34/0.53  thf('0', plain,
% 0.34/0.53      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.34/0.53        | ((k7_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('1', plain,
% 0.34/0.53      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.34/0.53       ~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('2', plain,
% 0.34/0.53      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)
% 0.34/0.53        | ((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('3', plain,
% 0.34/0.53      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.34/0.53         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.34/0.53      inference('split', [status(esa)], ['2'])).
% 0.34/0.53  thf(t90_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ B ) =>
% 0.34/0.53       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.34/0.53         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.34/0.53  thf('4', plain,
% 0.34/0.53      (![X42 : $i, X43 : $i]:
% 0.34/0.53         (((k1_relat_1 @ (k7_relat_1 @ X42 @ X43))
% 0.34/0.53            = (k3_xboole_0 @ (k1_relat_1 @ X42) @ X43))
% 0.34/0.53          | ~ (v1_relat_1 @ X42))),
% 0.34/0.53      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.34/0.53  thf(t12_setfam_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.34/0.53  thf('5', plain,
% 0.34/0.53      (![X34 : $i, X35 : $i]:
% 0.34/0.53         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 0.34/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.34/0.53  thf('6', plain,
% 0.34/0.53      (![X42 : $i, X43 : $i]:
% 0.34/0.53         (((k1_relat_1 @ (k7_relat_1 @ X42 @ X43))
% 0.34/0.53            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X42) @ X43)))
% 0.34/0.53          | ~ (v1_relat_1 @ X42))),
% 0.34/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.34/0.53  thf('7', plain,
% 0.34/0.53      (((((k1_relat_1 @ k1_xboole_0)
% 0.34/0.53           = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.34/0.53         | ~ (v1_relat_1 @ sk_B_1)))
% 0.34/0.53         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.34/0.53      inference('sup+', [status(thm)], ['3', '6'])).
% 0.34/0.53  thf(t60_relat_1, axiom,
% 0.34/0.53    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.34/0.53     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.34/0.53  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.34/0.53      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.34/0.53  thf('9', plain, ((v1_relat_1 @ sk_B_1)),
% 0.34/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.53  thf('10', plain,
% 0.34/0.53      ((((k1_xboole_0)
% 0.34/0.53          = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ sk_B_1) @ sk_A))))
% 0.34/0.53         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.34/0.53      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.34/0.53  thf(d7_xboole_0, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.34/0.53       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.34/0.53  thf('11', plain,
% 0.34/0.53      (![X0 : $i, X2 : $i]:
% 0.34/0.53         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.34/0.53      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.34/0.53  thf('12', plain,
% 0.34/0.53      (![X34 : $i, X35 : $i]:
% 0.34/0.53         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 0.34/0.53      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.34/0.53  thf('13', plain,
% 0.34/0.53      (![X0 : $i, X2 : $i]:
% 0.34/0.53         ((r1_xboole_0 @ X0 @ X2)
% 0.34/0.53          | ((k1_setfam_1 @ (k2_tarski @ X0 @ X2)) != (k1_xboole_0)))),
% 0.34/0.53      inference('demod', [status(thm)], ['11', '12'])).
% 0.34/0.53  thf('14', plain,
% 0.34/0.53      (((((k1_xboole_0) != (k1_xboole_0))
% 0.34/0.53         | (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))
% 0.34/0.53         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.34/0.53      inference('sup-', [status(thm)], ['10', '13'])).
% 0.34/0.53  thf('15', plain,
% 0.34/0.53      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.34/0.53         <= ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.34/0.53      inference('simplify', [status(thm)], ['14'])).
% 0.34/0.53  thf('16', plain,
% 0.34/0.53      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.34/0.53         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['0'])).
% 0.34/0.53  thf('17', plain,
% 0.34/0.53      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.34/0.53       ~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.34/0.53  thf('18', plain,
% 0.34/0.53      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.34/0.53       (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.34/0.53      inference('split', [status(esa)], ['2'])).
% 0.34/0.53  thf('19', plain,
% 0.34/0.53      (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A))
% 0.34/0.53         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.34/0.53      inference('split', [status(esa)], ['2'])).
% 0.34/0.53  thf(dt_k7_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.34/0.53  thf('20', plain,
% 0.34/0.53      (![X36 : $i, X37 : $i]:
% 0.34/0.53         (~ (v1_relat_1 @ X36) | (v1_relat_1 @ (k7_relat_1 @ X36 @ X37)))),
% 0.34/0.53      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.34/0.53  thf('21', plain,
% 0.34/0.53      (![X42 : $i, X43 : $i]:
% 0.34/0.53         (((k1_relat_1 @ (k7_relat_1 @ X42 @ X43))
% 0.34/0.53            = (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X42) @ X43)))
% 0.34/0.53          | ~ (v1_relat_1 @ X42))),
% 0.34/0.53      inference('demod', [status(thm)], ['4', '5'])).
% 0.34/0.53  thf(t56_relat_1, axiom,
% 0.34/0.53    (![A:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ A ) =>
% 0.34/0.53       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.34/0.53         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.34/0.53  thf('22', plain,
% 0.34/0.53      (![X41 : $i]:
% 0.34/0.53         ((r2_hidden @ (k4_tarski @ (sk_B @ X41) @ (sk_C_1 @ X41)) @ X41)
% 0.34/0.53          | ((X41) = (k1_xboole_0))
% 0.34/0.53          | ~ (v1_relat_1 @ X41))),
% 0.34/0.53      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.34/0.53  thf(t20_relat_1, axiom,
% 0.34/0.53    (![A:$i,B:$i,C:$i]:
% 0.34/0.53     ( ( v1_relat_1 @ C ) =>
% 0.34/0.53       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.34/0.53         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.34/0.53           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.34/0.53  thf('23', plain,
% 0.34/0.53      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.34/0.53         (~ (r2_hidden @ (k4_tarski @ X38 @ X39) @ X40)
% 0.34/0.53          | (r2_hidden @ X38 @ (k1_relat_1 @ X40))
% 0.34/0.53          | ~ (v1_relat_1 @ X40))),
% 0.34/0.53      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.34/0.54  thf('24', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         (~ (v1_relat_1 @ X0)
% 0.34/0.54          | ((X0) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_relat_1 @ X0)
% 0.34/0.54          | (r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.34/0.54  thf('25', plain,
% 0.34/0.54      (![X0 : $i]:
% 0.34/0.54         ((r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0))
% 0.34/0.54          | ((X0) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_relat_1 @ X0))),
% 0.34/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.34/0.54  thf('26', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         ((r2_hidden @ (sk_B @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.34/0.54           (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X1) @ X0)))
% 0.34/0.54          | ~ (v1_relat_1 @ X1)
% 0.34/0.54          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.34/0.54          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.34/0.54      inference('sup+', [status(thm)], ['21', '25'])).
% 0.34/0.54  thf('27', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         (~ (v1_relat_1 @ X1)
% 0.34/0.54          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_relat_1 @ X1)
% 0.34/0.54          | (r2_hidden @ (sk_B @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.34/0.54             (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X1) @ X0))))),
% 0.34/0.54      inference('sup-', [status(thm)], ['20', '26'])).
% 0.34/0.54  thf('28', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         ((r2_hidden @ (sk_B @ (k7_relat_1 @ X1 @ X0)) @ 
% 0.34/0.54           (k1_setfam_1 @ (k2_tarski @ (k1_relat_1 @ X1) @ X0)))
% 0.34/0.54          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.34/0.54          | ~ (v1_relat_1 @ X1))),
% 0.34/0.54      inference('simplify', [status(thm)], ['27'])).
% 0.34/0.54  thf(t4_xboole_0, axiom,
% 0.34/0.54    (![A:$i,B:$i]:
% 0.34/0.54     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.34/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.34/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.34/0.54            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.34/0.54  thf('29', plain,
% 0.34/0.54      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.34/0.54          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.34/0.54      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.34/0.54  thf('30', plain,
% 0.34/0.54      (![X34 : $i, X35 : $i]:
% 0.34/0.54         ((k1_setfam_1 @ (k2_tarski @ X34 @ X35)) = (k3_xboole_0 @ X34 @ X35))),
% 0.34/0.54      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.34/0.54  thf('31', plain,
% 0.34/0.54      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.34/0.54         (~ (r2_hidden @ X5 @ (k1_setfam_1 @ (k2_tarski @ X3 @ X6)))
% 0.34/0.54          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.34/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.34/0.54  thf('32', plain,
% 0.34/0.54      (![X0 : $i, X1 : $i]:
% 0.34/0.54         (~ (v1_relat_1 @ X1)
% 0.34/0.54          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.34/0.54          | ~ (r1_xboole_0 @ (k1_relat_1 @ X1) @ X0))),
% 0.34/0.54      inference('sup-', [status(thm)], ['28', '31'])).
% 0.34/0.54  thf('33', plain,
% 0.34/0.54      (((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))
% 0.34/0.54         | ~ (v1_relat_1 @ sk_B_1)))
% 0.34/0.54         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['19', '32'])).
% 0.34/0.54  thf('34', plain, ((v1_relat_1 @ sk_B_1)),
% 0.34/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.34/0.54  thf('35', plain,
% 0.34/0.54      ((((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))
% 0.34/0.54         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.34/0.54      inference('demod', [status(thm)], ['33', '34'])).
% 0.34/0.54  thf('36', plain,
% 0.34/0.54      ((((k7_relat_1 @ sk_B_1 @ sk_A) != (k1_xboole_0)))
% 0.34/0.54         <= (~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))))),
% 0.34/0.54      inference('split', [status(esa)], ['0'])).
% 0.34/0.54  thf('37', plain,
% 0.34/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.34/0.54         <= (~ (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0))) & 
% 0.34/0.54             ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)))),
% 0.34/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.34/0.54  thf('38', plain,
% 0.34/0.54      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B_1) @ sk_A)) | 
% 0.34/0.54       (((k7_relat_1 @ sk_B_1 @ sk_A) = (k1_xboole_0)))),
% 0.34/0.54      inference('simplify', [status(thm)], ['37'])).
% 0.34/0.54  thf('39', plain, ($false),
% 0.34/0.54      inference('sat_resolution*', [status(thm)], ['1', '17', '18', '38'])).
% 0.34/0.54  
% 0.34/0.54  % SZS output end Refutation
% 0.34/0.54  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
