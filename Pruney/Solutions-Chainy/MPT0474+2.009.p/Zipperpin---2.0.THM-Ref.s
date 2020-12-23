%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zow7GyOnZy

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:55 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 106 expanded)
%              Number of leaves         :   30 (  46 expanded)
%              Depth                    :   10
%              Number of atoms          :  363 ( 569 expanded)
%              Number of equality atoms :   49 (  82 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('0',plain,(
    ! [X41: $i] :
      ( ( v1_relat_1 @ X41 )
      | ( r2_hidden @ ( sk_B @ X41 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ o_0_0_xboole_0 )
      = X8 ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('4',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('5',plain,(
    ! [X8: $i] :
      ( ( k6_subset_1 @ X8 @ o_0_0_xboole_0 )
      = X8 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('9',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k6_subset_1 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ o_0_0_xboole_0 ) ),
    inference(condensation,[status(thm)],['10'])).

thf('12',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['0','11'])).

thf(t41_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) )
            = ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( v1_relat_1 @ X51 )
      | ( ( k4_relat_1 @ ( k6_subset_1 @ X52 @ X51 ) )
        = ( k6_subset_1 @ ( k4_relat_1 @ X52 ) @ ( k4_relat_1 @ X51 ) ) )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t41_relat_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t93_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X32 @ X33 ) )
      = ( k2_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t93_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('17',plain,(
    ! [X31: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t101_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t101_xboole_1])).

thf('20',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k6_subset_1 @ X34 @ X35 )
      = ( k4_xboole_0 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('21',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k5_xboole_0 @ X6 @ X7 )
      = ( k6_subset_1 @ ( k2_xboole_0 @ X6 @ X7 ) @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k6_subset_1 @ X0 @ ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('23',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X9: $i] :
      ( ( k5_xboole_0 @ X9 @ X9 )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('27',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X37 @ X38 ) )
      = ( k3_xboole_0 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('29',plain,(
    ! [X36: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X36 ) )
      = X36 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','25','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
        = ( k4_relat_1 @ ( k6_subset_1 @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( o_0_0_xboole_0
      = ( k6_subset_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','25','30'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( o_0_0_xboole_0
        = ( k4_relat_1 @ o_0_0_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( o_0_0_xboole_0
        = ( k4_relat_1 @ o_0_0_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf(t66_relat_1,conjecture,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t66_relat_1])).

thf('36',plain,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('38',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('39',plain,(
    ( k4_relat_1 @ o_0_0_xboole_0 )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['35','39'])).

thf('41',plain,(
    $false ),
    inference('sup-',[status(thm)],['12','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zow7GyOnZy
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:48:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 50 iterations in 0.028s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.19/0.48  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.19/0.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.19/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.48  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.48  thf(d1_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) <=>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ~( ( r2_hidden @ B @ A ) & 
% 0.19/0.48              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.19/0.48  thf('0', plain,
% 0.19/0.48      (![X41 : $i]: ((v1_relat_1 @ X41) | (r2_hidden @ (sk_B @ X41) @ X41))),
% 0.19/0.48      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.19/0.48  thf(t3_boole, axiom,
% 0.19/0.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.19/0.48  thf('1', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.19/0.48      inference('cnf', [status(esa)], [t3_boole])).
% 0.19/0.48  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.19/0.48  thf('2', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.48      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.48  thf('3', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ o_0_0_xboole_0) = (X8))),
% 0.19/0.48      inference('demod', [status(thm)], ['1', '2'])).
% 0.19/0.48  thf(redefinition_k6_subset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      (![X34 : $i, X35 : $i]:
% 0.19/0.48         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.48  thf('5', plain, (![X8 : $i]: ((k6_subset_1 @ X8 @ o_0_0_xboole_0) = (X8))),
% 0.19/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.19/0.48  thf(d5_xboole_0, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.19/0.48       ( ![D:$i]:
% 0.19/0.48         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.48           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.19/0.48  thf('6', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X4 @ X3)
% 0.19/0.48          | ~ (r2_hidden @ X4 @ X2)
% 0.19/0.48          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.19/0.48  thf('7', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X4 @ X2)
% 0.19/0.48          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X34 : $i, X35 : $i]:
% 0.19/0.48         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X4 @ X2)
% 0.19/0.48          | ~ (r2_hidden @ X4 @ (k6_subset_1 @ X1 @ X2)))),
% 0.19/0.48      inference('demod', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]:
% 0.19/0.48         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ o_0_0_xboole_0))),
% 0.19/0.48      inference('sup-', [status(thm)], ['5', '9'])).
% 0.19/0.48  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ o_0_0_xboole_0)),
% 0.19/0.48      inference('condensation', [status(thm)], ['10'])).
% 0.19/0.48  thf('12', plain, ((v1_relat_1 @ o_0_0_xboole_0)),
% 0.19/0.48      inference('sup-', [status(thm)], ['0', '11'])).
% 0.19/0.48  thf(t41_relat_1, axiom,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( v1_relat_1 @ A ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( v1_relat_1 @ B ) =>
% 0.19/0.48           ( ( k4_relat_1 @ ( k6_subset_1 @ A @ B ) ) =
% 0.19/0.48             ( k6_subset_1 @ ( k4_relat_1 @ A ) @ ( k4_relat_1 @ B ) ) ) ) ) ))).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      (![X51 : $i, X52 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X51)
% 0.19/0.48          | ((k4_relat_1 @ (k6_subset_1 @ X52 @ X51))
% 0.19/0.49              = (k6_subset_1 @ (k4_relat_1 @ X52) @ (k4_relat_1 @ X51)))
% 0.19/0.49          | ~ (v1_relat_1 @ X52))),
% 0.19/0.49      inference('cnf', [status(esa)], [t41_relat_1])).
% 0.19/0.49  thf(t69_enumset1, axiom,
% 0.19/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.19/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.49  thf(t93_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X32 : $i, X33 : $i]:
% 0.19/0.49         ((k3_tarski @ (k2_tarski @ X32 @ X33)) = (k2_xboole_0 @ X32 @ X33))),
% 0.19/0.49      inference('cnf', [status(esa)], [t93_zfmisc_1])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X0 : $i]: ((k3_tarski @ (k1_tarski @ X0)) = (k2_xboole_0 @ X0 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf(t31_zfmisc_1, axiom,
% 0.19/0.49    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.19/0.49  thf('17', plain, (![X31 : $i]: ((k3_tarski @ (k1_tarski @ X31)) = (X31))),
% 0.19/0.49      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.19/0.49  thf('18', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf(t101_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k5_xboole_0 @ A @ B ) =
% 0.19/0.49       ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i]:
% 0.19/0.49         ((k5_xboole_0 @ X6 @ X7)
% 0.19/0.49           = (k4_xboole_0 @ (k2_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t101_xboole_1])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      (![X34 : $i, X35 : $i]:
% 0.19/0.49         ((k6_subset_1 @ X34 @ X35) = (k4_xboole_0 @ X34 @ X35))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      (![X6 : $i, X7 : $i]:
% 0.19/0.49         ((k5_xboole_0 @ X6 @ X7)
% 0.19/0.49           = (k6_subset_1 @ (k2_xboole_0 @ X6 @ X7) @ (k3_xboole_0 @ X6 @ X7)))),
% 0.19/0.49      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k5_xboole_0 @ X0 @ X0)
% 0.19/0.49           = (k6_subset_1 @ X0 @ (k3_xboole_0 @ X0 @ X0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['18', '21'])).
% 0.19/0.49  thf(t92_xboole_1, axiom,
% 0.19/0.49    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.19/0.49  thf('23', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.19/0.49  thf('24', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.49  thf('25', plain, (![X9 : $i]: ((k5_xboole_0 @ X9 @ X9) = (o_0_0_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.19/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.49  thf(t12_setfam_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      (![X37 : $i, X38 : $i]:
% 0.19/0.49         ((k1_setfam_1 @ (k2_tarski @ X37 @ X38)) = (k3_xboole_0 @ X37 @ X38))),
% 0.19/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      (![X0 : $i]: ((k1_setfam_1 @ (k1_tarski @ X0)) = (k3_xboole_0 @ X0 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['26', '27'])).
% 0.19/0.49  thf(t11_setfam_1, axiom,
% 0.19/0.49    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.19/0.49  thf('29', plain, (![X36 : $i]: ((k1_setfam_1 @ (k1_tarski @ X36)) = (X36))),
% 0.19/0.49      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.19/0.49  thf('30', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain, (![X0 : $i]: ((o_0_0_xboole_0) = (k6_subset_1 @ X0 @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['22', '25', '30'])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((o_0_0_xboole_0) = (k4_relat_1 @ (k6_subset_1 @ X0 @ X0)))
% 0.19/0.49          | ~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('sup+', [status(thm)], ['13', '31'])).
% 0.19/0.49  thf('33', plain, (![X0 : $i]: ((o_0_0_xboole_0) = (k6_subset_1 @ X0 @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['22', '25', '30'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (((o_0_0_xboole_0) = (k4_relat_1 @ o_0_0_xboole_0))
% 0.19/0.49          | ~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         (~ (v1_relat_1 @ X0)
% 0.19/0.49          | ((o_0_0_xboole_0) = (k4_relat_1 @ o_0_0_xboole_0)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.49  thf(t66_relat_1, conjecture,
% 0.19/0.49    (( k4_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (( k4_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t66_relat_1])).
% 0.19/0.49  thf('36', plain, (((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('37', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.49  thf('38', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.19/0.49      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.19/0.49  thf('39', plain, (((k4_relat_1 @ o_0_0_xboole_0) != (o_0_0_xboole_0))),
% 0.19/0.49      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.19/0.49  thf('40', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.19/0.49      inference('simplify_reflect-', [status(thm)], ['35', '39'])).
% 0.19/0.49  thf('41', plain, ($false), inference('sup-', [status(thm)], ['12', '40'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
