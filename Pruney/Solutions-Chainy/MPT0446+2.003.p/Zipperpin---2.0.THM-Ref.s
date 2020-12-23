%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d3BHyd4soC

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:51 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   61 (  84 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :  329 ( 632 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t30_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
         => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
            & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relat_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X37: $i] :
      ( ( ( k3_relat_1 @ X37 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('3',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X38 @ X39 ) @ X40 )
      | ( r2_hidden @ X38 @ ( k1_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['2','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( $false
   <= ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['1','14'])).

thf('16',plain,(
    ! [X37: $i] :
      ( ( ( k3_relat_1 @ X37 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('17',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X38 @ X39 ) @ X40 )
      | ( r2_hidden @ X39 @ ( k2_relat_1 @ X40 ) )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r2_hidden @ sk_B @ ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X4: $i,X5: $i] :
      ( r1_tarski @ X4 @ ( k2_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_B @ ( k2_xboole_0 @ X0 @ ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['21','30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['16','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) )
   <= ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,(
    r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) )
    | ~ ( r2_hidden @ sk_B @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_C_1 ) ) ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['15','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d3BHyd4soC
% 0.11/0.33  % Computer   : n008.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 19:11:15 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running portfolio for 600 s
% 0.11/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 0.18/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.50  % Solved by: fo/fo7.sh
% 0.18/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.50  % done 153 iterations in 0.058s
% 0.18/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.50  % SZS output start Refutation
% 0.18/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.18/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.18/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.50  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.18/0.50  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.18/0.50  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.18/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.18/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.18/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.18/0.50  thf(t30_relat_1, conjecture,
% 0.18/0.50    (![A:$i,B:$i,C:$i]:
% 0.18/0.50     ( ( v1_relat_1 @ C ) =>
% 0.18/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.18/0.50         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.18/0.50           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.18/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.50    (~( ![A:$i,B:$i,C:$i]:
% 0.18/0.50        ( ( v1_relat_1 @ C ) =>
% 0.18/0.50          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.18/0.50            ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.18/0.50              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )),
% 0.18/0.50    inference('cnf.neg', [status(esa)], [t30_relat_1])).
% 0.18/0.50  thf('0', plain,
% 0.18/0.50      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.18/0.50        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('1', plain,
% 0.18/0.50      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)))
% 0.18/0.50         <= (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))))),
% 0.18/0.50      inference('split', [status(esa)], ['0'])).
% 0.18/0.50  thf(d6_relat_1, axiom,
% 0.18/0.50    (![A:$i]:
% 0.18/0.50     ( ( v1_relat_1 @ A ) =>
% 0.18/0.50       ( ( k3_relat_1 @ A ) =
% 0.18/0.50         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.18/0.50  thf('2', plain,
% 0.18/0.50      (![X37 : $i]:
% 0.18/0.50         (((k3_relat_1 @ X37)
% 0.18/0.50            = (k2_xboole_0 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37)))
% 0.18/0.50          | ~ (v1_relat_1 @ X37))),
% 0.18/0.50      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.18/0.50  thf('3', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf(t20_relat_1, axiom,
% 0.18/0.50    (![A:$i,B:$i,C:$i]:
% 0.18/0.50     ( ( v1_relat_1 @ C ) =>
% 0.18/0.50       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.18/0.50         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.18/0.50           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.18/0.50  thf('4', plain,
% 0.18/0.50      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.18/0.50         (~ (r2_hidden @ (k4_tarski @ X38 @ X39) @ X40)
% 0.18/0.50          | (r2_hidden @ X38 @ (k1_relat_1 @ X40))
% 0.18/0.50          | ~ (v1_relat_1 @ X40))),
% 0.18/0.50      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.18/0.50  thf('5', plain,
% 0.18/0.50      ((~ (v1_relat_1 @ sk_C_1) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.18/0.50  thf('6', plain, ((v1_relat_1 @ sk_C_1)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('7', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.18/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.18/0.50  thf(t7_xboole_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.18/0.50  thf('8', plain,
% 0.18/0.50      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.18/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.18/0.50  thf(d3_tarski, axiom,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.18/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.18/0.50  thf('9', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.18/0.50          | (r2_hidden @ X0 @ X2)
% 0.18/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.18/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.18/0.50  thf('10', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.50         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.18/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.18/0.50  thf('11', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (r2_hidden @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.18/0.50      inference('sup-', [status(thm)], ['7', '10'])).
% 0.18/0.50  thf('12', plain,
% 0.18/0.50      (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.18/0.50      inference('sup+', [status(thm)], ['2', '11'])).
% 0.18/0.50  thf('13', plain, ((v1_relat_1 @ sk_C_1)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('14', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.18/0.50      inference('demod', [status(thm)], ['12', '13'])).
% 0.18/0.50  thf('15', plain,
% 0.18/0.50      (($false) <= (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))))),
% 0.18/0.50      inference('demod', [status(thm)], ['1', '14'])).
% 0.18/0.50  thf('16', plain,
% 0.18/0.50      (![X37 : $i]:
% 0.18/0.50         (((k3_relat_1 @ X37)
% 0.18/0.50            = (k2_xboole_0 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37)))
% 0.18/0.50          | ~ (v1_relat_1 @ X37))),
% 0.18/0.50      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.18/0.50  thf('17', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('18', plain,
% 0.18/0.50      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.18/0.50         (~ (r2_hidden @ (k4_tarski @ X38 @ X39) @ X40)
% 0.18/0.50          | (r2_hidden @ X39 @ (k2_relat_1 @ X40))
% 0.18/0.50          | ~ (v1_relat_1 @ X40))),
% 0.18/0.50      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.18/0.50  thf('19', plain,
% 0.18/0.50      ((~ (v1_relat_1 @ sk_C_1) | (r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.18/0.50  thf('20', plain, ((v1_relat_1 @ sk_C_1)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('21', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_1))),
% 0.18/0.50      inference('demod', [status(thm)], ['19', '20'])).
% 0.18/0.50  thf(commutativity_k2_tarski, axiom,
% 0.18/0.50    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.18/0.50  thf('22', plain,
% 0.18/0.50      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.18/0.50      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.18/0.50  thf(l51_zfmisc_1, axiom,
% 0.18/0.50    (![A:$i,B:$i]:
% 0.18/0.50     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.18/0.50  thf('23', plain,
% 0.18/0.50      (![X35 : $i, X36 : $i]:
% 0.18/0.50         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.18/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.18/0.50  thf('24', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]:
% 0.18/0.50         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.18/0.50  thf('25', plain,
% 0.18/0.50      (![X35 : $i, X36 : $i]:
% 0.18/0.50         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.18/0.50      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.18/0.50  thf('26', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.18/0.50      inference('sup+', [status(thm)], ['24', '25'])).
% 0.18/0.50  thf('27', plain,
% 0.18/0.50      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.18/0.50      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.18/0.50  thf('28', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.18/0.50      inference('sup+', [status(thm)], ['26', '27'])).
% 0.18/0.50  thf('29', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.18/0.50          | (r2_hidden @ X0 @ X2)
% 0.18/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.18/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.18/0.50  thf('30', plain,
% 0.18/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.18/0.50         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X0))),
% 0.18/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.18/0.50  thf('31', plain,
% 0.18/0.50      (![X0 : $i]:
% 0.18/0.50         (r2_hidden @ sk_B @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['21', '30'])).
% 0.18/0.50  thf('32', plain,
% 0.18/0.50      (((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.18/0.50      inference('sup+', [status(thm)], ['16', '31'])).
% 0.18/0.50  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 0.18/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.50  thf('34', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))),
% 0.18/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.18/0.50  thf('35', plain,
% 0.18/0.50      ((~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))
% 0.18/0.50         <= (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))))),
% 0.18/0.50      inference('split', [status(esa)], ['0'])).
% 0.18/0.50  thf('36', plain, (((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))),
% 0.18/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.18/0.50  thf('37', plain,
% 0.18/0.50      (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))) | 
% 0.18/0.50       ~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))),
% 0.18/0.50      inference('split', [status(esa)], ['0'])).
% 0.18/0.50  thf('38', plain, (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)))),
% 0.18/0.50      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 0.18/0.50  thf('39', plain, ($false),
% 0.18/0.50      inference('simpl_trail', [status(thm)], ['15', '38'])).
% 0.18/0.50  
% 0.18/0.50  % SZS output end Refutation
% 0.18/0.50  
% 0.18/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
