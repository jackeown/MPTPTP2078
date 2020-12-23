%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RxiYKfHzfP

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:14 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 101 expanded)
%              Number of leaves         :   27 (  42 expanded)
%              Depth                    :   14
%              Number of atoms          :  466 ( 895 expanded)
%              Number of equality atoms :   26 (  40 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) )
        = ( k9_relat_1 @ X14 @ X15 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t167_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t167_funct_1])).

thf('1',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X10 ) @ X11 )
      | ( r2_hidden @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X18 @ X16 ) @ X17 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('9',plain,(
    ! [X22: $i] :
      ( ( ( k7_relat_1 @ X22 @ ( k1_relat_1 @ X22 ) )
        = X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) ) )
      | ( r2_hidden @ X19 @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('18',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19','20'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ ( k1_relat_1 @ X24 ) )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X24 ) )
      | ( ( k9_relat_1 @ X24 @ ( k2_tarski @ X23 @ X25 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X24 @ X23 ) @ ( k1_funct_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('33',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['4','31','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RxiYKfHzfP
% 0.14/0.36  % Computer   : n003.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:30:27 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.37  % Number of cores: 8
% 0.14/0.37  % Python version: Python 3.6.8
% 0.14/0.37  % Running in FO mode
% 0.45/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.66  % Solved by: fo/fo7.sh
% 0.45/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.66  % done 230 iterations in 0.194s
% 0.45/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.66  % SZS output start Refutation
% 0.45/0.66  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.45/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.66  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.66  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.45/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.66  thf(t148_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ B ) =>
% 0.45/0.66       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.45/0.66  thf('0', plain,
% 0.45/0.66      (![X14 : $i, X15 : $i]:
% 0.45/0.66         (((k2_relat_1 @ (k7_relat_1 @ X14 @ X15)) = (k9_relat_1 @ X14 @ X15))
% 0.45/0.66          | ~ (v1_relat_1 @ X14))),
% 0.45/0.66      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.45/0.66  thf(t167_funct_1, conjecture,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66       ( r1_tarski @
% 0.45/0.66         ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.45/0.66         ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ))).
% 0.45/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.66    (~( ![A:$i,B:$i]:
% 0.45/0.66        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.45/0.66          ( r1_tarski @
% 0.45/0.66            ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.45/0.66            ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )),
% 0.45/0.66    inference('cnf.neg', [status(esa)], [t167_funct_1])).
% 0.45/0.66  thf('1', plain,
% 0.45/0.66      (~ (r1_tarski @ 
% 0.45/0.66          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.45/0.66          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('2', plain,
% 0.45/0.66      ((~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.45/0.66           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.66      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.66  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('4', plain,
% 0.45/0.66      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.45/0.66          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['2', '3'])).
% 0.45/0.66  thf(dt_k7_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.45/0.66  thf('5', plain,
% 0.45/0.66      (![X12 : $i, X13 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X12) | (v1_relat_1 @ (k7_relat_1 @ X12 @ X13)))),
% 0.45/0.66      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.45/0.66  thf(l27_zfmisc_1, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.45/0.66  thf('6', plain,
% 0.45/0.66      (![X10 : $i, X11 : $i]:
% 0.45/0.66         ((r1_xboole_0 @ (k1_tarski @ X10) @ X11) | (r2_hidden @ X10 @ X11))),
% 0.45/0.66      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.45/0.66  thf(t207_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ C ) =>
% 0.45/0.66       ( ( r1_xboole_0 @ A @ B ) =>
% 0.45/0.66         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.66  thf('7', plain,
% 0.45/0.66      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.45/0.66         (~ (r1_xboole_0 @ X16 @ X17)
% 0.45/0.66          | ~ (v1_relat_1 @ X18)
% 0.45/0.66          | ((k7_relat_1 @ (k7_relat_1 @ X18 @ X16) @ X17) = (k1_xboole_0)))),
% 0.45/0.66      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.45/0.66  thf('8', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.66         ((r2_hidden @ X1 @ X0)
% 0.45/0.66          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ (k1_tarski @ X1)) @ X0)
% 0.45/0.66              = (k1_xboole_0))
% 0.45/0.66          | ~ (v1_relat_1 @ X2))),
% 0.45/0.66      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.66  thf(t98_relat_1, axiom,
% 0.45/0.66    (![A:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ A ) =>
% 0.45/0.66       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.45/0.66  thf('9', plain,
% 0.45/0.66      (![X22 : $i]:
% 0.45/0.66         (((k7_relat_1 @ X22 @ (k1_relat_1 @ X22)) = (X22))
% 0.45/0.66          | ~ (v1_relat_1 @ X22))),
% 0.45/0.66      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.45/0.66  thf('10', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0)))
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | (r2_hidden @ X0 @ 
% 0.45/0.66             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_tarski @ X0))))
% 0.45/0.66          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ (k1_tarski @ X0))))),
% 0.45/0.66      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.66  thf('11', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X1)
% 0.45/0.66          | (r2_hidden @ X0 @ 
% 0.45/0.66             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_tarski @ X0))))
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0))))),
% 0.45/0.66      inference('sup-', [status(thm)], ['5', '10'])).
% 0.45/0.66  thf('12', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0)))
% 0.45/0.66          | (r2_hidden @ X0 @ 
% 0.45/0.66             (k1_relat_1 @ (k7_relat_1 @ X1 @ (k1_tarski @ X0))))
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('simplify', [status(thm)], ['11'])).
% 0.45/0.66  thf(t86_relat_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( v1_relat_1 @ C ) =>
% 0.45/0.66       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.45/0.66         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.45/0.66  thf('13', plain,
% 0.45/0.66      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X19 @ (k1_relat_1 @ (k7_relat_1 @ X21 @ X20)))
% 0.45/0.66          | (r2_hidden @ X19 @ (k1_relat_1 @ X21))
% 0.45/0.66          | ~ (v1_relat_1 @ X21))),
% 0.45/0.66      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.45/0.66  thf('14', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ X1)
% 0.45/0.66          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0)))
% 0.45/0.66          | ~ (v1_relat_1 @ X1)
% 0.45/0.66          | (r2_hidden @ X0 @ (k1_relat_1 @ X1)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.66  thf('15', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]:
% 0.45/0.66         ((r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.45/0.66          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0)))
% 0.45/0.66          | ~ (v1_relat_1 @ X1))),
% 0.45/0.66      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.66  thf('16', plain,
% 0.45/0.66      (~ (r1_tarski @ 
% 0.45/0.66          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.45/0.66          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('17', plain,
% 0.45/0.66      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.45/0.66           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.45/0.66        | ~ (v1_relat_1 @ sk_B)
% 0.45/0.66        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.45/0.66  thf(t60_relat_1, axiom,
% 0.45/0.66    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.66     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.66  thf('18', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.66      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.66  thf('19', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.66  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('21', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.45/0.66  thf('22', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.45/0.66      inference('demod', [status(thm)], ['17', '18', '19', '20'])).
% 0.45/0.66  thf(t118_funct_1, axiom,
% 0.45/0.66    (![A:$i,B:$i,C:$i]:
% 0.45/0.66     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.66       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.45/0.66           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.45/0.66         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.45/0.66           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.45/0.66  thf('23', plain,
% 0.45/0.66      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.45/0.66         (~ (r2_hidden @ X23 @ (k1_relat_1 @ X24))
% 0.45/0.66          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X24))
% 0.45/0.66          | ((k9_relat_1 @ X24 @ (k2_tarski @ X23 @ X25))
% 0.45/0.66              = (k2_tarski @ (k1_funct_1 @ X24 @ X23) @ 
% 0.45/0.66                 (k1_funct_1 @ X24 @ X25)))
% 0.45/0.66          | ~ (v1_funct_1 @ X24)
% 0.45/0.66          | ~ (v1_relat_1 @ X24))),
% 0.45/0.66      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.45/0.66  thf('24', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (~ (v1_relat_1 @ sk_B)
% 0.45/0.66          | ~ (v1_funct_1 @ sk_B)
% 0.45/0.66          | ((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.45/0.66              = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.45/0.66                 (k1_funct_1 @ sk_B @ X0)))
% 0.45/0.66          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['22', '23'])).
% 0.45/0.66  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 0.45/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.66  thf('27', plain,
% 0.45/0.66      (![X0 : $i]:
% 0.45/0.66         (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.45/0.66            = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.45/0.66               (k1_funct_1 @ sk_B @ X0)))
% 0.45/0.66          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.45/0.66      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.45/0.66  thf('28', plain,
% 0.45/0.66      (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ sk_A))
% 0.45/0.66         = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('sup-', [status(thm)], ['21', '27'])).
% 0.45/0.66  thf(t69_enumset1, axiom,
% 0.45/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.66  thf('29', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.66  thf('30', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.45/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.66  thf('31', plain,
% 0.45/0.66      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.66         = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.45/0.66      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.45/0.66  thf(d10_xboole_0, axiom,
% 0.45/0.66    (![A:$i,B:$i]:
% 0.45/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.66  thf('32', plain,
% 0.45/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.66  thf('33', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.66      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.66  thf('34', plain, ($false),
% 0.45/0.66      inference('demod', [status(thm)], ['4', '31', '33'])).
% 0.45/0.66  
% 0.45/0.66  % SZS output end Refutation
% 0.45/0.66  
% 0.45/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
