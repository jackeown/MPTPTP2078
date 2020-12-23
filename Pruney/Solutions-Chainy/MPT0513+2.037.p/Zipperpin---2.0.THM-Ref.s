%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vY7G4yH0X1

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   62 (  70 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  274 ( 304 expanded)
%              Number of equality atoms :   43 (  51 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t111_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k7_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t111_relat_1])).

thf('0',plain,(
    ( k7_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ( k7_relat_1 @ o_0_0_xboole_0 @ sk_A )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,
    ( ( k1_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X45 ) @ X46 )
      | ( ( k7_relat_1 @ X45 @ X46 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ! [X45: $i,X46: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X45 ) @ X46 )
      | ( ( k7_relat_1 @ X45 @ X46 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ o_0_0_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 )
      | ( ( k7_relat_1 @ o_0_0_xboole_0 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X2 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ o_0_0_xboole_0 @ ( k3_xboole_0 @ o_0_0_xboole_0 @ X2 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('19',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_xboole_0 @ X3 @ X5 )
      | ( ( k4_xboole_0 @ X3 @ X5 )
       != X3 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != X1 )
      | ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ o_0_0_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ o_0_0_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ o_0_0_xboole_0 )
      | ( ( k7_relat_1 @ o_0_0_xboole_0 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','22'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('24',plain,(
    ! [X42: $i] :
      ( ( v1_relat_1 @ X42 )
      | ( r2_hidden @ ( sk_B @ X42 ) @ X42 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t46_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
        = B ) ) )).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k2_xboole_0 @ ( k1_tarski @ X35 ) @ X34 )
        = X34 )
      | ~ ( r2_hidden @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t46_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( ( k2_xboole_0 @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('27',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X36 ) @ X37 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('28',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('29',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X36 ) @ X37 )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ o_0_0_xboole_0 @ X0 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['23','31'])).

thf('33',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['3','32'])).

thf('34',plain,(
    $false ),
    inference(simplify,[status(thm)],['33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vY7G4yH0X1
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:41:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 51 iterations in 0.020s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.46  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.46  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(t111_relat_1, conjecture,
% 0.20/0.46    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t111_relat_1])).
% 0.20/0.46  thf('0', plain, (((k7_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.46  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.46  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.46  thf('3', plain, (((k7_relat_1 @ o_0_0_xboole_0 @ sk_A) != (o_0_0_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.20/0.46  thf(t60_relat_1, axiom,
% 0.20/0.46    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.46     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.46  thf('4', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.46  thf('5', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.46  thf('6', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.46  thf('7', plain, (((k1_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.46  thf(t95_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.46         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X45 : $i, X46 : $i]:
% 0.20/0.46         (~ (r1_xboole_0 @ (k1_relat_1 @ X45) @ X46)
% 0.20/0.46          | ((k7_relat_1 @ X45 @ X46) = (k1_xboole_0))
% 0.20/0.46          | ~ (v1_relat_1 @ X45))),
% 0.20/0.46      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.46  thf('9', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X45 : $i, X46 : $i]:
% 0.20/0.46         (~ (r1_xboole_0 @ (k1_relat_1 @ X45) @ X46)
% 0.20/0.46          | ((k7_relat_1 @ X45 @ X46) = (o_0_0_xboole_0))
% 0.20/0.46          | ~ (v1_relat_1 @ X45))),
% 0.20/0.46      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r1_xboole_0 @ o_0_0_xboole_0 @ X0)
% 0.20/0.46          | ~ (v1_relat_1 @ o_0_0_xboole_0)
% 0.20/0.46          | ((k7_relat_1 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.46  thf(t4_boole, axiom,
% 0.20/0.46    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.46  thf('13', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.46  thf('14', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.46      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X2 : $i]: ((k4_xboole_0 @ o_0_0_xboole_0 @ X2) = (o_0_0_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.46  thf(t100_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.46           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X2 : $i]:
% 0.20/0.46         ((k5_xboole_0 @ o_0_0_xboole_0 @ (k3_xboole_0 @ o_0_0_xboole_0 @ X2))
% 0.20/0.46           = (o_0_0_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.46           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.46  thf(t83_xboole_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X3 : $i, X5 : $i]:
% 0.20/0.46         ((r1_xboole_0 @ X3 @ X5) | ((k4_xboole_0 @ X3 @ X5) != (X3)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) != (X1))
% 0.20/0.47          | (r1_xboole_0 @ X1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.20/0.47          | (r1_xboole_0 @ o_0_0_xboole_0 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '20'])).
% 0.20/0.47  thf('22', plain, (![X0 : $i]: (r1_xboole_0 @ o_0_0_xboole_0 @ X0)),
% 0.20/0.47      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ o_0_0_xboole_0)
% 0.20/0.47          | ((k7_relat_1 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['11', '22'])).
% 0.20/0.47  thf(d1_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) <=>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.47              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.47  thf('24', plain,
% 0.20/0.47      (![X42 : $i]: ((v1_relat_1 @ X42) | (r2_hidden @ (sk_B @ X42) @ X42))),
% 0.20/0.47      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.47  thf(t46_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r2_hidden @ A @ B ) =>
% 0.20/0.47       ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( B ) ) ))).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X34 : $i, X35 : $i]:
% 0.20/0.47         (((k2_xboole_0 @ (k1_tarski @ X35) @ X34) = (X34))
% 0.20/0.47          | ~ (r2_hidden @ X35 @ X34))),
% 0.20/0.47      inference('cnf', [status(esa)], [t46_zfmisc_1])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v1_relat_1 @ X0)
% 0.20/0.47          | ((k2_xboole_0 @ (k1_tarski @ (sk_B @ X0)) @ X0) = (X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.47  thf(t49_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X36 : $i, X37 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_tarski @ X36) @ X37) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.47  thf('28', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X36 : $i, X37 : $i]:
% 0.20/0.47         ((k2_xboole_0 @ (k1_tarski @ X36) @ X37) != (o_0_0_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X0 : $i]: (((X0) != (o_0_0_xboole_0)) | (v1_relat_1 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '29'])).
% 0.20/0.47  thf('31', plain, ((v1_relat_1 @ o_0_0_xboole_0)),
% 0.20/0.47      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (![X0 : $i]: ((k7_relat_1 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['23', '31'])).
% 0.20/0.47  thf('33', plain, (((o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['3', '32'])).
% 0.20/0.47  thf('34', plain, ($false), inference('simplify', [status(thm)], ['33'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
