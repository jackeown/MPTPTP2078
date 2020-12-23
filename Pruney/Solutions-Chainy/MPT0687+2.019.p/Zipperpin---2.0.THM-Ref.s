%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.97asJ11ehR

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:13 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 102 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  555 ( 950 expanded)
%              Number of equality atoms :   48 (  72 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t142_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
        <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_1])).

thf('0',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k10_relat_1 @ X27 @ X28 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X27 ) @ X28 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('6',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','15'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t72_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
    <=> ( ~ ( r2_hidden @ A @ C )
        & ~ ( r2_hidden @ B @ C ) ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ( ( k4_xboole_0 @ ( k2_tarski @ X23 @ X25 ) @ X24 )
       != ( k2_tarski @ X23 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
       != ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( ( k1_tarski @ sk_A )
       != ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','25'])).

thf('27',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('28',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('29',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X23 @ X25 ) @ X26 )
        = ( k2_tarski @ X23 @ X25 ) )
      | ( r2_hidden @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t72_zfmisc_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r1_xboole_0 @ X10 @ X12 )
      | ( ( k4_xboole_0 @ X10 @ X12 )
       != X10 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X27 ) @ X28 )
      | ( ( k10_relat_1 @ X27 @ X28 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
   <= ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 )
   <= ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
       != k1_xboole_0 )
      & ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','26','27','47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.97asJ11ehR
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:01:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 155 iterations in 0.085s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.37/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.54  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.37/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.37/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.37/0.54  thf(t142_funct_1, conjecture,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ B ) =>
% 0.37/0.54       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.37/0.54         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i,B:$i]:
% 0.37/0.54        ( ( v1_relat_1 @ B ) =>
% 0.37/0.54          ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.37/0.54            ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t142_funct_1])).
% 0.37/0.54  thf('0', plain,
% 0.37/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.37/0.54        | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.37/0.54       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.37/0.54      inference('split', [status(esa)], ['0'])).
% 0.37/0.54  thf('2', plain,
% 0.37/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0))
% 0.37/0.54        | (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('3', plain,
% 0.37/0.54      (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.37/0.54         <= (((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.37/0.54      inference('split', [status(esa)], ['2'])).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.37/0.54         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.37/0.54      inference('split', [status(esa)], ['0'])).
% 0.37/0.54  thf(t173_relat_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ B ) =>
% 0.37/0.54       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.37/0.54         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X27 : $i, X28 : $i]:
% 0.37/0.54         (((k10_relat_1 @ X27 @ X28) != (k1_xboole_0))
% 0.37/0.54          | (r1_xboole_0 @ (k2_relat_1 @ X27) @ X28)
% 0.37/0.54          | ~ (v1_relat_1 @ X27))),
% 0.37/0.54      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.37/0.54  thf('6', plain,
% 0.37/0.54      (((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.54         | ~ (v1_relat_1 @ sk_B)
% 0.37/0.54         | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.37/0.54         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.37/0.54  thf('7', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (((((k1_xboole_0) != (k1_xboole_0))
% 0.37/0.54         | (r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A))))
% 0.37/0.54         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.37/0.54      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (((r1_xboole_0 @ (k2_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))
% 0.37/0.54         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.37/0.54      inference('simplify', [status(thm)], ['8'])).
% 0.37/0.54  thf(t3_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.37/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.37/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.37/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.37/0.54  thf('10', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X6))),
% 0.37/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.37/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X8 @ X6)
% 0.37/0.54          | ~ (r2_hidden @ X8 @ X9)
% 0.37/0.54          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.37/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X1 @ X0)
% 0.37/0.54          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.37/0.54          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.37/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf('14', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X0 @ X1)
% 0.37/0.54          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.37/0.54          | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['10', '13'])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_B)))
% 0.37/0.54         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['9', '15'])).
% 0.37/0.54  thf(t83_xboole_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X10 : $i, X11 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_xboole_0 @ X10 @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_B))
% 0.37/0.54          = (k1_tarski @ sk_A)))
% 0.37/0.54         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['16', '17'])).
% 0.37/0.54  thf(t69_enumset1, axiom,
% 0.37/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.37/0.54  thf('19', plain,
% 0.37/0.54      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.54  thf(t72_zfmisc_1, axiom,
% 0.37/0.54    (![A:$i,B:$i,C:$i]:
% 0.37/0.54     ( ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.37/0.54       ( ( ~( r2_hidden @ A @ C ) ) & ( ~( r2_hidden @ B @ C ) ) ) ))).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.37/0.54         (~ (r2_hidden @ X23 @ X24)
% 0.37/0.54          | ((k4_xboole_0 @ (k2_tarski @ X23 @ X25) @ X24)
% 0.37/0.54              != (k2_tarski @ X23 @ X25)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.37/0.54  thf('21', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k2_tarski @ X0 @ X0))
% 0.37/0.54          | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) != (k1_tarski @ X0))
% 0.37/0.54          | ~ (r2_hidden @ X0 @ X1))),
% 0.37/0.54      inference('demod', [status(thm)], ['21', '22'])).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      (((((k1_tarski @ sk_A) != (k1_tarski @ sk_A))
% 0.37/0.54         | ~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))
% 0.37/0.54         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['18', '23'])).
% 0.37/0.54  thf('25', plain,
% 0.37/0.54      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.37/0.54         <= ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.37/0.54      inference('simplify', [status(thm)], ['24'])).
% 0.37/0.54  thf('26', plain,
% 0.37/0.54      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.37/0.54       ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['3', '25'])).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.37/0.54       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.37/0.54      inference('split', [status(esa)], ['2'])).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.54  thf('29', plain,
% 0.37/0.54      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ (k2_tarski @ X23 @ X25) @ X26)
% 0.37/0.54            = (k2_tarski @ X23 @ X25))
% 0.37/0.54          | (r2_hidden @ X25 @ X26)
% 0.37/0.54          | (r2_hidden @ X23 @ X26))),
% 0.37/0.54      inference('cnf', [status(esa)], [t72_zfmisc_1])).
% 0.37/0.54  thf('30', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k2_tarski @ X0 @ X0))
% 0.37/0.54          | (r2_hidden @ X0 @ X1)
% 0.37/0.54          | (r2_hidden @ X0 @ X1))),
% 0.37/0.54      inference('sup+', [status(thm)], ['28', '29'])).
% 0.37/0.54  thf('31', plain,
% 0.37/0.54      (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.37/0.54  thf('32', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.37/0.54          | (r2_hidden @ X0 @ X1)
% 0.37/0.54          | (r2_hidden @ X0 @ X1))),
% 0.37/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.37/0.54  thf('33', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r2_hidden @ X0 @ X1)
% 0.37/0.54          | ((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['32'])).
% 0.37/0.54  thf('34', plain,
% 0.37/0.54      (![X10 : $i, X12 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ X10 @ X12) | ((k4_xboole_0 @ X10 @ X12) != (X10)))),
% 0.37/0.54      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.37/0.54  thf('35', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((k1_tarski @ X0) != (k1_tarski @ X0))
% 0.37/0.54          | (r2_hidden @ X0 @ X1)
% 0.37/0.54          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.37/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.37/0.54  thf('36', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r1_xboole_0 @ (k1_tarski @ X0) @ X1) | (r2_hidden @ X0 @ X1))),
% 0.37/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.37/0.54  thf('37', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.37/0.54      inference('simplify', [status(thm)], ['14'])).
% 0.37/0.54  thf('38', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.37/0.54  thf('39', plain,
% 0.37/0.54      (![X27 : $i, X28 : $i]:
% 0.37/0.54         (~ (r1_xboole_0 @ (k2_relat_1 @ X27) @ X28)
% 0.37/0.54          | ((k10_relat_1 @ X27 @ X28) = (k1_xboole_0))
% 0.37/0.54          | ~ (v1_relat_1 @ X27))),
% 0.37/0.54      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.37/0.54  thf('40', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.37/0.54          | ~ (v1_relat_1 @ X1)
% 0.37/0.54          | ((k10_relat_1 @ X1 @ (k1_tarski @ X0)) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.37/0.54  thf('41', plain,
% 0.37/0.54      ((~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.37/0.54         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.37/0.54      inference('split', [status(esa)], ['0'])).
% 0.37/0.54  thf('42', plain,
% 0.37/0.54      (((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))
% 0.37/0.54         | ~ (v1_relat_1 @ sk_B)))
% 0.37/0.54         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['40', '41'])).
% 0.37/0.54  thf('43', plain, ((v1_relat_1 @ sk_B)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('44', plain,
% 0.37/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0)))
% 0.37/0.54         <= (~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.37/0.54      inference('demod', [status(thm)], ['42', '43'])).
% 0.37/0.54  thf('45', plain,
% 0.37/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) != (k1_xboole_0)))
% 0.37/0.54         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))))),
% 0.37/0.54      inference('split', [status(esa)], ['2'])).
% 0.37/0.54  thf('46', plain,
% 0.37/0.54      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.54         <= (~ (((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) & 
% 0.37/0.54             ~ ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.37/0.54  thf('47', plain,
% 0.37/0.54      ((((k10_relat_1 @ sk_B @ (k1_tarski @ sk_A)) = (k1_xboole_0))) | 
% 0.37/0.54       ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.37/0.54      inference('simplify', [status(thm)], ['46'])).
% 0.37/0.54  thf('48', plain, ($false),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['1', '26', '27', '47'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
