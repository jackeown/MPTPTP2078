%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FZWx5peHzs

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  203 ( 241 expanded)
%              Number of equality atoms :   30 (  37 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t168_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k10_relat_1 @ B @ A )
        = ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k10_relat_1 @ X33 @ X34 )
        = ( k10_relat_1 @ X33 @ ( k3_xboole_0 @ ( k2_relat_1 @ X33 ) @ X34 ) ) )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t168_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
        = ( k10_relat_1 @ k1_xboole_0 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k2_tarski @ X2 @ X1 )
      = ( k2_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X30 @ X31 ) )
      = ( k3_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X30 @ X31 ) )
      = ( k3_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('11',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('12',plain,(
    ! [X32: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','10','13'])).

thf('15',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X35: $i] :
      ( ( ( k10_relat_1 @ X35 @ ( k2_relat_1 @ X35 ) )
        = ( k1_relat_1 @ X35 ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf('17',plain,
    ( ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('19',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('20',plain,
    ( ( k10_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['14','20'])).

thf('22',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FZWx5peHzs
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:10:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 31 iterations in 0.015s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.22/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.48  thf(t172_relat_1, conjecture,
% 0.22/0.48    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.22/0.48  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t60_relat_1, axiom,
% 0.22/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.48  thf(t168_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( k10_relat_1 @ B @ A ) =
% 0.22/0.48         ( k10_relat_1 @ B @ ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X33 : $i, X34 : $i]:
% 0.22/0.48         (((k10_relat_1 @ X33 @ X34)
% 0.22/0.48            = (k10_relat_1 @ X33 @ (k3_xboole_0 @ (k2_relat_1 @ X33) @ X34)))
% 0.22/0.48          | ~ (v1_relat_1 @ X33))),
% 0.22/0.48      inference('cnf', [status(esa)], [t168_relat_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.22/0.48            = (k10_relat_1 @ k1_xboole_0 @ (k3_xboole_0 @ k1_xboole_0 @ X0)))
% 0.22/0.48          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf(commutativity_k2_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.22/0.48  thf('4', plain,
% 0.22/0.48      (![X1 : $i, X2 : $i]: ((k2_tarski @ X2 @ X1) = (k2_tarski @ X1 @ X2))),
% 0.22/0.48      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.22/0.48  thf(t12_setfam_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.22/0.48  thf('5', plain,
% 0.22/0.48      (![X30 : $i, X31 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k2_tarski @ X30 @ X31)) = (k3_xboole_0 @ X30 @ X31))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X30 : $i, X31 : $i]:
% 0.22/0.48         ((k1_setfam_1 @ (k2_tarski @ X30 @ X31)) = (k3_xboole_0 @ X30 @ X31))),
% 0.22/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.22/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.22/0.48  thf(t2_boole, axiom,
% 0.22/0.48    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t2_boole])).
% 0.22/0.48  thf('10', plain,
% 0.22/0.48      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.48  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.22/0.48  thf('11', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.22/0.48  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.22/0.48  thf('12', plain, (![X32 : $i]: (v1_relat_1 @ (k6_relat_1 @ X32))),
% 0.22/0.48      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.22/0.48  thf('13', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.48      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         ((k10_relat_1 @ k1_xboole_0 @ X0)
% 0.22/0.48           = (k10_relat_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '10', '13'])).
% 0.22/0.48  thf('15', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.48  thf(t169_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X35 : $i]:
% 0.22/0.48         (((k10_relat_1 @ X35 @ (k2_relat_1 @ X35)) = (k1_relat_1 @ X35))
% 0.22/0.48          | ~ (v1_relat_1 @ X35))),
% 0.22/0.48      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      ((((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_relat_1 @ k1_xboole_0))
% 0.22/0.48        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.48      inference('sup+', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.48  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.48      inference('sup+', [status(thm)], ['11', '12'])).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (((k10_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      (![X0 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['14', '20'])).
% 0.22/0.48  thf('22', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '21'])).
% 0.22/0.48  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
