%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U30FxywaVY

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  63 expanded)
%              Number of leaves         :   22 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  231 ( 259 expanded)
%              Number of equality atoms :   36 (  44 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ( k9_relat_1 @ o_0_0_xboole_0 @ sk_A )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1','2'])).

thf(t111_relat_1,axiom,(
    ! [A: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X37: $i] :
      ( ( k7_relat_1 @ k1_xboole_0 @ X37 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t111_relat_1])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ! [X37: $i] :
      ( ( k7_relat_1 @ o_0_0_xboole_0 @ X37 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X38 @ X39 ) )
        = ( k9_relat_1 @ X38 @ X39 ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
        = ( k9_relat_1 @ o_0_0_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
        = ( k9_relat_1 @ o_0_0_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','13'])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('15',plain,(
    ! [X34: $i] :
      ( ( v1_relat_1 @ X34 )
      | ( r2_hidden @ ( sk_B @ X34 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X12 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('19',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ o_0_0_xboole_0 @ X12 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ X29 )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X12: $i] :
      ( ( k6_subset_1 @ o_0_0_xboole_0 @ X12 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( X5
       != ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('23',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k4_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k6_subset_1 @ X28 @ X29 )
      = ( k4_xboole_0 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('25',plain,(
    ! [X3: $i,X4: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k6_subset_1 @ X3 @ X4 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference(condensation,[status(thm)],['26'])).

thf('28',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['15','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k9_relat_1 @ o_0_0_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','28'])).

thf('30',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['3','29'])).

thf('31',plain,(
    $false ),
    inference(simplify,[status(thm)],['30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U30FxywaVY
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:52:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 50 iterations in 0.027s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.48  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.48  thf(t150_relat_1, conjecture,
% 0.20/0.48    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.20/0.48  thf('0', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.48  thf('1', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.48  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.48  thf('3', plain, (((k9_relat_1 @ o_0_0_xboole_0 @ sk_A) != (o_0_0_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['0', '1', '2'])).
% 0.20/0.48  thf(t111_relat_1, axiom,
% 0.20/0.48    (![A:$i]: ( ( k7_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('4', plain,
% 0.20/0.48      (![X37 : $i]: ((k7_relat_1 @ k1_xboole_0 @ X37) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t111_relat_1])).
% 0.20/0.48  thf('5', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.48  thf('6', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X37 : $i]: ((k7_relat_1 @ o_0_0_xboole_0 @ X37) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.48  thf(t148_relat_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ B ) =>
% 0.20/0.48       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.48  thf('8', plain,
% 0.20/0.48      (![X38 : $i, X39 : $i]:
% 0.20/0.48         (((k2_relat_1 @ (k7_relat_1 @ X38 @ X39)) = (k9_relat_1 @ X38 @ X39))
% 0.20/0.48          | ~ (v1_relat_1 @ X38))),
% 0.20/0.48      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.48  thf('9', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((k2_relat_1 @ o_0_0_xboole_0) = (k9_relat_1 @ o_0_0_xboole_0 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.48      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.48  thf(t60_relat_1, axiom,
% 0.20/0.48    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.48     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('10', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.48  thf('11', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.48  thf('12', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.48  thf('13', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (((o_0_0_xboole_0) = (k9_relat_1 @ o_0_0_xboole_0 @ X0))
% 0.20/0.48          | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['9', '13'])).
% 0.20/0.48  thf(d1_relat_1, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( v1_relat_1 @ A ) <=>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ~( ( r2_hidden @ B @ A ) & 
% 0.20/0.48              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.48  thf('15', plain,
% 0.20/0.48      (![X34 : $i]: ((v1_relat_1 @ X34) | (r2_hidden @ (sk_B @ X34) @ X34))),
% 0.20/0.48      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.20/0.48  thf(t4_boole, axiom,
% 0.20/0.48    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X12 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X12) = (k1_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.48  thf('17', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.48  thf('18', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.48  thf('19', plain,
% 0.20/0.48      (![X12 : $i]: ((k4_xboole_0 @ o_0_0_xboole_0 @ X12) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.48  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.48  thf('20', plain,
% 0.20/0.48      (![X28 : $i, X29 : $i]:
% 0.20/0.48         ((k6_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.48  thf('21', plain,
% 0.20/0.48      (![X12 : $i]: ((k6_subset_1 @ o_0_0_xboole_0 @ X12) = (o_0_0_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.48  thf(d5_xboole_0, axiom,
% 0.20/0.48    (![A:$i,B:$i,C:$i]:
% 0.20/0.48     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.48       ( ![D:$i]:
% 0.20/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.48           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X6 @ X5)
% 0.20/0.48          | ~ (r2_hidden @ X6 @ X4)
% 0.20/0.48          | ((X5) != (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.48  thf('23', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.48          | ~ (r2_hidden @ X6 @ (k4_xboole_0 @ X3 @ X4)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (![X28 : $i, X29 : $i]:
% 0.20/0.48         ((k6_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))),
% 0.20/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.48  thf('25', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i, X6 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X6 @ X4)
% 0.20/0.48          | ~ (r2_hidden @ X6 @ (k6_subset_1 @ X3 @ X4)))),
% 0.20/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.48  thf('26', plain,
% 0.20/0.48      (![X0 : $i, X1 : $i]:
% 0.20/0.48         (~ (r2_hidden @ X1 @ o_0_0_xboole_0) | ~ (r2_hidden @ X1 @ X0))),
% 0.20/0.48      inference('sup-', [status(thm)], ['21', '25'])).
% 0.20/0.48  thf('27', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.20/0.48      inference('condensation', [status(thm)], ['26'])).
% 0.20/0.48  thf('28', plain, ((v1_relat_1 @ o_0_0_xboole_0)),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '27'])).
% 0.20/0.48  thf('29', plain,
% 0.20/0.48      (![X0 : $i]: ((o_0_0_xboole_0) = (k9_relat_1 @ o_0_0_xboole_0 @ X0))),
% 0.20/0.48      inference('demod', [status(thm)], ['14', '28'])).
% 0.20/0.48  thf('30', plain, (((o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '29'])).
% 0.20/0.48  thf('31', plain, ($false), inference('simplify', [status(thm)], ['30'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
