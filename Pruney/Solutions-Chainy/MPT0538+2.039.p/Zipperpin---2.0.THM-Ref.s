%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S5GPUxTA6h

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:54 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   53 (  92 expanded)
%              Number of leaves         :   24 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  252 ( 510 expanded)
%              Number of equality atoms :   30 (  61 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t138_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k8_relat_1 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k8_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t138_relat_1])).

thf('0',plain,(
    ( k8_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('3',plain,(
    ! [X44: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X44 ) @ X44 )
        = X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('4',plain,
    ( ( ( k8_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('5',plain,(
    ! [X41: $i] :
      ( ( v1_relat_1 @ X41 )
      | ( r2_hidden @ ( sk_B @ X41 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X1 @ X2 )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33 != X35 )
      | ~ ( r2_hidden @ X33 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('10',plain,(
    ! [X34: $i,X35: $i] :
      ~ ( r2_hidden @ X35 @ ( k4_xboole_0 @ X34 @ ( k1_tarski @ X35 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k5_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('13',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','13'])).

thf('15',plain,
    ( ( k8_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['4','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('18',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r1_tarski @ X45 @ X46 )
      | ~ ( v1_relat_1 @ X47 )
      | ( ( k8_relat_1 @ X46 @ ( k8_relat_1 @ X45 @ X47 ) )
        = ( k8_relat_1 @ X45 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ k1_xboole_0 @ X1 ) )
        = ( k8_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ k1_xboole_0 )
        = ( k8_relat_1 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ k1_xboole_0 @ ( k5_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','15'])).

thf('22',plain,(
    ! [X4: $i] :
      ( ( k5_xboole_0 @ X4 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','13'])).

thf('24',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( k8_relat_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21','24'])).

thf('26',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.S5GPUxTA6h
% 0.12/0.31  % Computer   : n011.cluster.edu
% 0.12/0.31  % Model      : x86_64 x86_64
% 0.12/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.31  % Memory     : 8042.1875MB
% 0.12/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.31  % CPULimit   : 60
% 0.12/0.31  % DateTime   : Tue Dec  1 16:22:42 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.31  % Running portfolio for 600 s
% 0.17/0.31  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.31  % Number of cores: 8
% 0.17/0.32  % Python version: Python 3.6.8
% 0.17/0.32  % Running in FO mode
% 0.17/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.17/0.47  % Solved by: fo/fo7.sh
% 0.17/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.17/0.47  % done 149 iterations in 0.045s
% 0.17/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.17/0.47  % SZS output start Refutation
% 0.17/0.47  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.17/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.17/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.17/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.17/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.17/0.47  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.17/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.17/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.17/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.17/0.47  thf(sk_B_type, type, sk_B: $i > $i).
% 0.17/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.17/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.17/0.47  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.17/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.17/0.47  thf(t138_relat_1, conjecture,
% 0.17/0.47    (![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.17/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.17/0.47    (~( ![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.17/0.47    inference('cnf.neg', [status(esa)], [t138_relat_1])).
% 0.17/0.47  thf('0', plain, (((k8_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.17/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.17/0.47  thf(t92_xboole_1, axiom,
% 0.17/0.47    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.17/0.47  thf('1', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.17/0.47      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.17/0.47  thf(t60_relat_1, axiom,
% 0.17/0.47    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.17/0.47     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.17/0.47  thf('2', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.17/0.47      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.17/0.47  thf(t126_relat_1, axiom,
% 0.17/0.47    (![A:$i]:
% 0.17/0.47     ( ( v1_relat_1 @ A ) =>
% 0.17/0.47       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.17/0.47  thf('3', plain,
% 0.17/0.47      (![X44 : $i]:
% 0.17/0.47         (((k8_relat_1 @ (k2_relat_1 @ X44) @ X44) = (X44))
% 0.17/0.47          | ~ (v1_relat_1 @ X44))),
% 0.17/0.47      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.17/0.47  thf('4', plain,
% 0.17/0.47      ((((k8_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.17/0.47        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.17/0.47      inference('sup+', [status(thm)], ['2', '3'])).
% 0.17/0.47  thf(d1_relat_1, axiom,
% 0.17/0.47    (![A:$i]:
% 0.17/0.47     ( ( v1_relat_1 @ A ) <=>
% 0.17/0.47       ( ![B:$i]:
% 0.17/0.47         ( ~( ( r2_hidden @ B @ A ) & 
% 0.17/0.47              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.17/0.47  thf('5', plain,
% 0.17/0.47      (![X41 : $i]: ((v1_relat_1 @ X41) | (r2_hidden @ (sk_B @ X41) @ X41))),
% 0.17/0.47      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.17/0.47  thf(idempotence_k3_xboole_0, axiom,
% 0.17/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.17/0.47  thf('6', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.17/0.47      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.17/0.47  thf(t100_xboole_1, axiom,
% 0.17/0.47    (![A:$i,B:$i]:
% 0.17/0.47     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.17/0.47  thf('7', plain,
% 0.17/0.47      (![X1 : $i, X2 : $i]:
% 0.17/0.47         ((k4_xboole_0 @ X1 @ X2)
% 0.17/0.47           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.17/0.47      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.17/0.47  thf('8', plain,
% 0.17/0.47      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.17/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.17/0.47  thf(t64_zfmisc_1, axiom,
% 0.17/0.47    (![A:$i,B:$i,C:$i]:
% 0.17/0.47     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.17/0.47       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.17/0.47  thf('9', plain,
% 0.17/0.47      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.17/0.47         (((X33) != (X35))
% 0.17/0.47          | ~ (r2_hidden @ X33 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X35))))),
% 0.17/0.47      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.17/0.47  thf('10', plain,
% 0.17/0.47      (![X34 : $i, X35 : $i]:
% 0.17/0.47         ~ (r2_hidden @ X35 @ (k4_xboole_0 @ X34 @ (k1_tarski @ X35)))),
% 0.17/0.47      inference('simplify', [status(thm)], ['9'])).
% 0.17/0.47  thf('11', plain,
% 0.17/0.47      (![X0 : $i]:
% 0.17/0.47         ~ (r2_hidden @ X0 @ 
% 0.17/0.47            (k5_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X0)))),
% 0.17/0.47      inference('sup-', [status(thm)], ['8', '10'])).
% 0.17/0.47  thf('12', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.17/0.47      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.17/0.47  thf('13', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.17/0.47      inference('demod', [status(thm)], ['11', '12'])).
% 0.17/0.47  thf('14', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.17/0.47      inference('sup-', [status(thm)], ['5', '13'])).
% 0.17/0.47  thf('15', plain,
% 0.17/0.47      (((k8_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.17/0.47      inference('demod', [status(thm)], ['4', '14'])).
% 0.17/0.47  thf('16', plain,
% 0.17/0.47      (![X0 : $i]:
% 0.17/0.47         ((k8_relat_1 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.17/0.47      inference('sup+', [status(thm)], ['1', '15'])).
% 0.17/0.47  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.17/0.47  thf('17', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.17/0.47      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.17/0.47  thf(t129_relat_1, axiom,
% 0.17/0.47    (![A:$i,B:$i,C:$i]:
% 0.17/0.47     ( ( v1_relat_1 @ C ) =>
% 0.17/0.47       ( ( r1_tarski @ A @ B ) =>
% 0.17/0.47         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.17/0.47  thf('18', plain,
% 0.17/0.47      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.17/0.47         (~ (r1_tarski @ X45 @ X46)
% 0.17/0.47          | ~ (v1_relat_1 @ X47)
% 0.17/0.47          | ((k8_relat_1 @ X46 @ (k8_relat_1 @ X45 @ X47))
% 0.17/0.47              = (k8_relat_1 @ X45 @ X47)))),
% 0.17/0.47      inference('cnf', [status(esa)], [t129_relat_1])).
% 0.17/0.47  thf('19', plain,
% 0.17/0.47      (![X0 : $i, X1 : $i]:
% 0.17/0.47         (((k8_relat_1 @ X0 @ (k8_relat_1 @ k1_xboole_0 @ X1))
% 0.17/0.47            = (k8_relat_1 @ k1_xboole_0 @ X1))
% 0.17/0.47          | ~ (v1_relat_1 @ X1))),
% 0.17/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.17/0.47  thf('20', plain,
% 0.17/0.47      (![X0 : $i, X1 : $i]:
% 0.17/0.47         (((k8_relat_1 @ X1 @ k1_xboole_0)
% 0.17/0.47            = (k8_relat_1 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)))
% 0.17/0.47          | ~ (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0)))),
% 0.17/0.47      inference('sup+', [status(thm)], ['16', '19'])).
% 0.17/0.47  thf('21', plain,
% 0.17/0.47      (![X0 : $i]:
% 0.17/0.47         ((k8_relat_1 @ k1_xboole_0 @ (k5_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.17/0.47      inference('sup+', [status(thm)], ['1', '15'])).
% 0.17/0.47  thf('22', plain, (![X4 : $i]: ((k5_xboole_0 @ X4 @ X4) = (k1_xboole_0))),
% 0.17/0.47      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.17/0.47  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.17/0.47      inference('sup-', [status(thm)], ['5', '13'])).
% 0.17/0.47  thf('24', plain, (![X0 : $i]: (v1_relat_1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.17/0.47      inference('sup+', [status(thm)], ['22', '23'])).
% 0.17/0.47  thf('25', plain,
% 0.17/0.47      (![X1 : $i]: ((k8_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.17/0.47      inference('demod', [status(thm)], ['20', '21', '24'])).
% 0.17/0.47  thf('26', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.17/0.47      inference('demod', [status(thm)], ['0', '25'])).
% 0.17/0.47  thf('27', plain, ($false), inference('simplify', [status(thm)], ['26'])).
% 0.17/0.47  
% 0.17/0.47  % SZS output end Refutation
% 0.17/0.47  
% 0.17/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
