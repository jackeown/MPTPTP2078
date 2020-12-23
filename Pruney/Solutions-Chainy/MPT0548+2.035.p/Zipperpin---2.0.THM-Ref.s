%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fgmKZXBR13

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  55 expanded)
%              Number of leaves         :   28 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  265 ( 265 expanded)
%              Number of equality atoms :   36 (  36 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t150_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k9_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t150_relat_1])).

thf('0',plain,(
    ( k9_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t111_relat_1,axiom,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X47: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X47 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X48 @ X49 ) )
        = ( k9_relat_1 @ X48 @ X49 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('6',plain,(
    ! [X44: $i] :
      ( ( v1_relat_1 @ X44 )
      | ( r2_hidden @ ( sk_B @ X44 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X32: $i,X34: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X32 ) @ X34 )
      | ~ ( r2_hidden @ X32 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_B @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('10',plain,
    ( ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k1_tarski @ ( sk_B @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('12',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38 != X37 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X38 ) @ ( k1_tarski @ X37 ) )
       != ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('13',plain,(
    ! [X37: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X37 ) @ ( k1_tarski @ X37 ) )
     != ( k1_tarski @ X37 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X0 ) )
     != ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X35 ) @ ( k2_tarski @ X35 @ X36 ) )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

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
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('18',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(demod,[status(thm)],['14','19'])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','20'])).

thf('22',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','22'])).

thf('24',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fgmKZXBR13
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:31:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 305 iterations in 0.109s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.57  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.57  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.57  thf(t150_relat_1, conjecture,
% 0.20/0.57    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.20/0.57  thf('0', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(t111_relat_1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      (![X47 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X47) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t111_relat_1])).
% 0.20/0.57  thf(t148_relat_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ B ) =>
% 0.20/0.57       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X48 : $i, X49 : $i]:
% 0.20/0.57         (((k2_relat_1 @ (k7_relat_1 @ X48 @ X49)) = (k9_relat_1 @ X48 @ X49))
% 0.20/0.57          | ~ (v1_relat_1 @ X48))),
% 0.20/0.57      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.57      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.57  thf(t60_relat_1, axiom,
% 0.20/0.57    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.57     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.57  thf('4', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         (((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.57          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.57  thf(d1_relat_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ A ) <=>
% 0.20/0.57       ( ![B:$i]:
% 0.20/0.57         ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.57              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X44 : $i]: ((v1_relat_1 @ X44) | (r2_hidden @ (sk_B @ X44) @ X44))),
% 0.20/0.57      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.57  thf(l1_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (![X32 : $i, X34 : $i]:
% 0.20/0.57         ((r1_tarski @ (k1_tarski @ X32) @ X34) | ~ (r2_hidden @ X32 @ X34))),
% 0.20/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((v1_relat_1 @ X0) | (r1_tarski @ (k1_tarski @ (sk_B @ X0)) @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.57  thf(t3_xboole_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X2 : $i]: (((X2) = (k1_xboole_0)) | ~ (r1_tarski @ X2 @ k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.57  thf('10', plain,
% 0.20/0.57      (((v1_relat_1 @ k1_xboole_0)
% 0.20/0.57        | ((k1_tarski @ (sk_B @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.20/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.57  thf(t69_enumset1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.57  thf('11', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.20/0.57      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.57  thf(t20_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.20/0.57         ( k1_tarski @ A ) ) <=>
% 0.20/0.57       ( ( A ) != ( B ) ) ))).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X37 : $i, X38 : $i]:
% 0.20/0.57         (((X38) != (X37))
% 0.20/0.57          | ((k4_xboole_0 @ (k1_tarski @ X38) @ (k1_tarski @ X37))
% 0.20/0.57              != (k1_tarski @ X38)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      (![X37 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k1_tarski @ X37) @ (k1_tarski @ X37))
% 0.20/0.57           != (k1_tarski @ X37))),
% 0.20/0.57      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.57  thf('14', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X0))
% 0.20/0.57           != (k1_tarski @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.57  thf(t19_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.57       ( k1_tarski @ A ) ))).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X35 : $i, X36 : $i]:
% 0.20/0.57         ((k3_xboole_0 @ (k1_tarski @ X35) @ (k2_tarski @ X35 @ X36))
% 0.20/0.57           = (k1_tarski @ X35))),
% 0.20/0.57      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.57  thf(t100_xboole_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ X0 @ X1)
% 0.20/0.57           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.20/0.57      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.20/0.57           = (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.20/0.57      inference('sup+', [status(thm)], ['15', '16'])).
% 0.20/0.57  thf(t92_xboole_1, axiom,
% 0.20/0.57    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.57  thf('18', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.20/0.57      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i]:
% 0.20/0.57         ((k4_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X0 @ X1))
% 0.20/0.57           = (k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.57  thf('20', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['14', '19'])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      ((((k1_xboole_0) != (k1_xboole_0)) | (v1_relat_1 @ k1_xboole_0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['10', '20'])).
% 0.20/0.57  thf('22', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.57      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.57  thf('23', plain,
% 0.20/0.57      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.20/0.57      inference('demod', [status(thm)], ['5', '22'])).
% 0.20/0.57  thf('24', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.57      inference('demod', [status(thm)], ['0', '23'])).
% 0.20/0.57  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
