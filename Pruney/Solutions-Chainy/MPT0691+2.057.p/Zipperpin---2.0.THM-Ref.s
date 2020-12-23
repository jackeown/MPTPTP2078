%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HLdbiotGxF

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:25 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   66 (  98 expanded)
%              Number of leaves         :   19 (  35 expanded)
%              Depth                    :   16
%              Number of atoms          :  471 ( 842 expanded)
%              Number of equality atoms :   21 (  25 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t146_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
         => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X37 @ X38 ) )
        = ( k9_relat_1 @ X37 @ X38 ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X41: $i] :
      ( ( ( k10_relat_1 @ X41 @ ( k2_relat_1 @ X41 ) )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('5',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('6',plain,(
    ! [X57: $i,X58: $i] :
      ( ~ ( r1_tarski @ X57 @ ( k1_relat_1 @ X58 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X58 @ X57 ) )
        = X57 )
      | ~ ( v1_relat_1 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['7','8'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X39 @ X40 ) @ ( k1_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_A @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) )
      | ( sk_A
        = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = sk_A ),
    inference(demod,[status(thm)],['7','8'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['17','18','20'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A
      = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( sk_A
    = ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(t98_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = A ) ) )).

thf('29',plain,(
    ! [X61: $i] :
      ( ( ( k7_relat_1 @ X61 @ ( k1_relat_1 @ X61 ) )
        = X61 )
      | ~ ( v1_relat_1 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t98_relat_1])).

thf('30',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t104_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ) )).

thf('31',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r1_tarski @ X34 @ X35 )
      | ~ ( v1_relat_1 @ X36 )
      | ( r1_tarski @ ( k7_relat_1 @ X36 @ X34 ) @ ( k7_relat_1 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t104_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X0 @ sk_A ) @ ( k7_relat_1 @ X0 @ ( k1_relat_1 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    r1_tarski @ ( k7_relat_1 @ sk_B @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ( r1_tarski @ ( k10_relat_1 @ X43 @ X44 ) @ ( k10_relat_1 @ X42 @ X44 ) )
      | ~ ( r1_tarski @ X43 @ X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ ( k10_relat_1 @ sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ ( k10_relat_1 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['27','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HLdbiotGxF
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.71  % Solved by: fo/fo7.sh
% 0.53/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.71  % done 537 iterations in 0.275s
% 0.53/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.71  % SZS output start Refutation
% 0.53/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.53/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.71  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.71  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.53/0.71  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.53/0.71  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.71  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.53/0.71  thf(t146_funct_1, conjecture,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ B ) =>
% 0.53/0.71       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.53/0.71         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.53/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.71    (~( ![A:$i,B:$i]:
% 0.53/0.71        ( ( v1_relat_1 @ B ) =>
% 0.53/0.71          ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.53/0.71            ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )),
% 0.53/0.71    inference('cnf.neg', [status(esa)], [t146_funct_1])).
% 0.53/0.71  thf('0', plain,
% 0.53/0.71      (~ (r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t148_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ B ) =>
% 0.53/0.71       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.53/0.71  thf('1', plain,
% 0.53/0.71      (![X37 : $i, X38 : $i]:
% 0.53/0.71         (((k2_relat_1 @ (k7_relat_1 @ X37 @ X38)) = (k9_relat_1 @ X37 @ X38))
% 0.53/0.71          | ~ (v1_relat_1 @ X37))),
% 0.53/0.71      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.53/0.71  thf(dt_k7_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.53/0.71  thf('2', plain,
% 0.53/0.71      (![X29 : $i, X30 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ X29) | (v1_relat_1 @ (k7_relat_1 @ X29 @ X30)))),
% 0.53/0.71      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.53/0.71  thf(t169_relat_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ A ) =>
% 0.53/0.71       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.53/0.71  thf('3', plain,
% 0.53/0.71      (![X41 : $i]:
% 0.53/0.71         (((k10_relat_1 @ X41 @ (k2_relat_1 @ X41)) = (k1_relat_1 @ X41))
% 0.53/0.71          | ~ (v1_relat_1 @ X41))),
% 0.53/0.71      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.53/0.71  thf('4', plain,
% 0.53/0.71      (![X29 : $i, X30 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ X29) | (v1_relat_1 @ (k7_relat_1 @ X29 @ X30)))),
% 0.53/0.71      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.53/0.71  thf('5', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t91_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ B ) =>
% 0.53/0.71       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.53/0.71         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.53/0.71  thf('6', plain,
% 0.53/0.71      (![X57 : $i, X58 : $i]:
% 0.53/0.71         (~ (r1_tarski @ X57 @ (k1_relat_1 @ X58))
% 0.53/0.71          | ((k1_relat_1 @ (k7_relat_1 @ X58 @ X57)) = (X57))
% 0.53/0.71          | ~ (v1_relat_1 @ X58))),
% 0.53/0.71      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.53/0.71  thf('7', plain,
% 0.53/0.71      ((~ (v1_relat_1 @ sk_B)
% 0.53/0.71        | ((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['5', '6'])).
% 0.53/0.71  thf('8', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('9', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.53/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.53/0.71  thf(t167_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ B ) =>
% 0.53/0.71       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 0.53/0.71  thf('10', plain,
% 0.53/0.71      (![X39 : $i, X40 : $i]:
% 0.53/0.71         ((r1_tarski @ (k10_relat_1 @ X39 @ X40) @ (k1_relat_1 @ X39))
% 0.53/0.71          | ~ (v1_relat_1 @ X39))),
% 0.53/0.71      inference('cnf', [status(esa)], [t167_relat_1])).
% 0.53/0.71  thf('11', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)
% 0.53/0.71          | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['9', '10'])).
% 0.53/0.71  thf('12', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ sk_B)
% 0.53/0.71          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A))),
% 0.53/0.71      inference('sup-', [status(thm)], ['4', '11'])).
% 0.53/0.71  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('14', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ sk_A)),
% 0.53/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.53/0.71  thf(d10_xboole_0, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.71  thf('15', plain,
% 0.53/0.71      (![X0 : $i, X2 : $i]:
% 0.53/0.71         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.53/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.71  thf('16', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (~ (r1_tarski @ sk_A @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0))
% 0.53/0.71          | ((sk_A) = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['14', '15'])).
% 0.53/0.71  thf('17', plain,
% 0.53/0.71      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))
% 0.53/0.71        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.53/0.71        | ((sk_A)
% 0.53/0.71            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.53/0.71               (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['3', '16'])).
% 0.53/0.71  thf('18', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) = (sk_A))),
% 0.53/0.71      inference('demod', [status(thm)], ['7', '8'])).
% 0.53/0.71  thf('19', plain,
% 0.53/0.71      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.53/0.71      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.71  thf('20', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.53/0.71      inference('simplify', [status(thm)], ['19'])).
% 0.53/0.71  thf('21', plain,
% 0.53/0.71      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.53/0.71        | ((sk_A)
% 0.53/0.71            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.53/0.71               (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))),
% 0.53/0.71      inference('demod', [status(thm)], ['17', '18', '20'])).
% 0.53/0.71  thf('22', plain,
% 0.53/0.71      ((~ (v1_relat_1 @ sk_B)
% 0.53/0.71        | ((sk_A)
% 0.53/0.71            = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.53/0.71               (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))))),
% 0.53/0.71      inference('sup-', [status(thm)], ['2', '21'])).
% 0.53/0.71  thf('23', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('24', plain,
% 0.53/0.71      (((sk_A)
% 0.53/0.71         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.53/0.71            (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))))),
% 0.53/0.71      inference('demod', [status(thm)], ['22', '23'])).
% 0.53/0.71  thf('25', plain,
% 0.53/0.71      ((((sk_A)
% 0.53/0.71          = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.53/0.71             (k9_relat_1 @ sk_B @ sk_A)))
% 0.53/0.71        | ~ (v1_relat_1 @ sk_B))),
% 0.53/0.71      inference('sup+', [status(thm)], ['1', '24'])).
% 0.53/0.71  thf('26', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('27', plain,
% 0.53/0.71      (((sk_A)
% 0.53/0.71         = (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ 
% 0.53/0.71            (k9_relat_1 @ sk_B @ sk_A)))),
% 0.53/0.71      inference('demod', [status(thm)], ['25', '26'])).
% 0.53/0.71  thf('28', plain,
% 0.53/0.71      (![X29 : $i, X30 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ X29) | (v1_relat_1 @ (k7_relat_1 @ X29 @ X30)))),
% 0.53/0.71      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.53/0.71  thf(t98_relat_1, axiom,
% 0.53/0.71    (![A:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ A ) =>
% 0.53/0.71       ( ( k7_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( A ) ) ))).
% 0.53/0.71  thf('29', plain,
% 0.53/0.71      (![X61 : $i]:
% 0.53/0.71         (((k7_relat_1 @ X61 @ (k1_relat_1 @ X61)) = (X61))
% 0.53/0.71          | ~ (v1_relat_1 @ X61))),
% 0.53/0.71      inference('cnf', [status(esa)], [t98_relat_1])).
% 0.53/0.71  thf('30', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf(t104_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i,C:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ C ) =>
% 0.53/0.71       ( ( r1_tarski @ A @ B ) =>
% 0.53/0.71         ( r1_tarski @ ( k7_relat_1 @ C @ A ) @ ( k7_relat_1 @ C @ B ) ) ) ))).
% 0.53/0.71  thf('31', plain,
% 0.53/0.71      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.53/0.71         (~ (r1_tarski @ X34 @ X35)
% 0.53/0.71          | ~ (v1_relat_1 @ X36)
% 0.53/0.71          | (r1_tarski @ (k7_relat_1 @ X36 @ X34) @ (k7_relat_1 @ X36 @ X35)))),
% 0.53/0.71      inference('cnf', [status(esa)], [t104_relat_1])).
% 0.53/0.71  thf('32', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         ((r1_tarski @ (k7_relat_1 @ X0 @ sk_A) @ 
% 0.53/0.71           (k7_relat_1 @ X0 @ (k1_relat_1 @ sk_B)))
% 0.53/0.71          | ~ (v1_relat_1 @ X0))),
% 0.53/0.71      inference('sup-', [status(thm)], ['30', '31'])).
% 0.53/0.71  thf('33', plain,
% 0.53/0.71      (((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A) @ sk_B)
% 0.53/0.71        | ~ (v1_relat_1 @ sk_B)
% 0.53/0.71        | ~ (v1_relat_1 @ sk_B))),
% 0.53/0.71      inference('sup+', [status(thm)], ['29', '32'])).
% 0.53/0.71  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('35', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('36', plain, ((r1_tarski @ (k7_relat_1 @ sk_B @ sk_A) @ sk_B)),
% 0.53/0.71      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.53/0.71  thf(t179_relat_1, axiom,
% 0.53/0.71    (![A:$i,B:$i]:
% 0.53/0.71     ( ( v1_relat_1 @ B ) =>
% 0.53/0.71       ( ![C:$i]:
% 0.53/0.71         ( ( v1_relat_1 @ C ) =>
% 0.53/0.71           ( ( r1_tarski @ B @ C ) =>
% 0.53/0.71             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.53/0.71  thf('37', plain,
% 0.53/0.71      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ X42)
% 0.53/0.71          | (r1_tarski @ (k10_relat_1 @ X43 @ X44) @ (k10_relat_1 @ X42 @ X44))
% 0.53/0.71          | ~ (r1_tarski @ X43 @ X42)
% 0.53/0.71          | ~ (v1_relat_1 @ X43))),
% 0.53/0.71      inference('cnf', [status(esa)], [t179_relat_1])).
% 0.53/0.71  thf('38', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.53/0.71          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ 
% 0.53/0.71             (k10_relat_1 @ sk_B @ X0))
% 0.53/0.71          | ~ (v1_relat_1 @ sk_B))),
% 0.53/0.71      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.71  thf('39', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('40', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.53/0.71          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ 
% 0.53/0.71             (k10_relat_1 @ sk_B @ X0)))),
% 0.53/0.71      inference('demod', [status(thm)], ['38', '39'])).
% 0.53/0.71  thf('41', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (~ (v1_relat_1 @ sk_B)
% 0.53/0.71          | (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ 
% 0.53/0.71             (k10_relat_1 @ sk_B @ X0)))),
% 0.53/0.71      inference('sup-', [status(thm)], ['28', '40'])).
% 0.53/0.71  thf('42', plain, ((v1_relat_1 @ sk_B)),
% 0.53/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.71  thf('43', plain,
% 0.53/0.71      (![X0 : $i]:
% 0.53/0.71         (r1_tarski @ (k10_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ 
% 0.53/0.71          (k10_relat_1 @ sk_B @ X0))),
% 0.53/0.71      inference('demod', [status(thm)], ['41', '42'])).
% 0.53/0.71  thf('44', plain,
% 0.53/0.71      ((r1_tarski @ sk_A @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)))),
% 0.53/0.71      inference('sup+', [status(thm)], ['27', '43'])).
% 0.53/0.71  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.53/0.71  
% 0.53/0.71  % SZS output end Refutation
% 0.53/0.71  
% 0.53/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
