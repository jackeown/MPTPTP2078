%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TSg9AEW71F

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:54 EST 2020

% Result     : Theorem 1.46s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   64 (  95 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  381 ( 710 expanded)
%              Number of equality atoms :   12 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t31_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( ( r1_tarski @ A @ B )
             => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X37: $i] :
      ( ( ( k3_relat_1 @ X37 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('2',plain,(
    ! [X37: $i] :
      ( ( ( k3_relat_1 @ X37 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( r1_tarski @ ( k1_relat_1 @ X39 ) @ ( k1_relat_1 @ X38 ) )
      | ~ ( r1_tarski @ X39 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('11',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X37: $i] :
      ( ( ( k3_relat_1 @ X37 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X37 ) @ ( k2_relat_1 @ X37 ) ) )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k2_tarski @ X29 @ X28 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X30: $i,X31: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X30 @ X31 ) )
      = ( k2_xboole_0 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ( r1_tarski @ ( k2_relat_1 @ X39 ) @ ( k2_relat_1 @ X38 ) )
      | ~ ( r1_tarski @ X39 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ X15 @ X16 )
      | ~ ( r1_tarski @ X16 @ X17 )
      | ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('36',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X25 @ X26 )
      | ~ ( r1_tarski @ X27 @ X26 )
      | ( r1_tarski @ ( k2_xboole_0 @ X25 @ X27 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ X0 ) @ ( k3_relat_1 @ sk_B ) )
      | ~ ( r1_tarski @ X0 @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k1_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('40',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup+',[status(thm)],['1','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r1_tarski @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['0','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.TSg9AEW71F
% 0.14/0.35  % Computer   : n001.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:17:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.46/1.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.46/1.68  % Solved by: fo/fo7.sh
% 1.46/1.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.46/1.68  % done 2778 iterations in 1.227s
% 1.46/1.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.46/1.68  % SZS output start Refutation
% 1.46/1.68  thf(sk_B_type, type, sk_B: $i).
% 1.46/1.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.46/1.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.46/1.68  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 1.46/1.68  thf(sk_A_type, type, sk_A: $i).
% 1.46/1.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.46/1.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.46/1.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.46/1.68  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.46/1.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.46/1.68  thf(t31_relat_1, conjecture,
% 1.46/1.68    (![A:$i]:
% 1.46/1.68     ( ( v1_relat_1 @ A ) =>
% 1.46/1.68       ( ![B:$i]:
% 1.46/1.68         ( ( v1_relat_1 @ B ) =>
% 1.46/1.68           ( ( r1_tarski @ A @ B ) =>
% 1.46/1.68             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 1.46/1.68  thf(zf_stmt_0, negated_conjecture,
% 1.46/1.68    (~( ![A:$i]:
% 1.46/1.68        ( ( v1_relat_1 @ A ) =>
% 1.46/1.68          ( ![B:$i]:
% 1.46/1.68            ( ( v1_relat_1 @ B ) =>
% 1.46/1.68              ( ( r1_tarski @ A @ B ) =>
% 1.46/1.68                ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 1.46/1.68    inference('cnf.neg', [status(esa)], [t31_relat_1])).
% 1.46/1.68  thf('0', plain, (~ (r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf(d6_relat_1, axiom,
% 1.46/1.68    (![A:$i]:
% 1.46/1.68     ( ( v1_relat_1 @ A ) =>
% 1.46/1.68       ( ( k3_relat_1 @ A ) =
% 1.46/1.68         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 1.46/1.68  thf('1', plain,
% 1.46/1.68      (![X37 : $i]:
% 1.46/1.68         (((k3_relat_1 @ X37)
% 1.46/1.68            = (k2_xboole_0 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37)))
% 1.46/1.68          | ~ (v1_relat_1 @ X37))),
% 1.46/1.68      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.46/1.68  thf('2', plain,
% 1.46/1.68      (![X37 : $i]:
% 1.46/1.68         (((k3_relat_1 @ X37)
% 1.46/1.68            = (k2_xboole_0 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37)))
% 1.46/1.68          | ~ (v1_relat_1 @ X37))),
% 1.46/1.68      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.46/1.68  thf(t7_xboole_1, axiom,
% 1.46/1.68    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 1.46/1.68  thf('3', plain,
% 1.46/1.68      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 1.46/1.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.46/1.68  thf('4', plain,
% 1.46/1.68      (![X0 : $i]:
% 1.46/1.68         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.46/1.68          | ~ (v1_relat_1 @ X0))),
% 1.46/1.68      inference('sup+', [status(thm)], ['2', '3'])).
% 1.46/1.68  thf('5', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf(t25_relat_1, axiom,
% 1.46/1.68    (![A:$i]:
% 1.46/1.68     ( ( v1_relat_1 @ A ) =>
% 1.46/1.68       ( ![B:$i]:
% 1.46/1.68         ( ( v1_relat_1 @ B ) =>
% 1.46/1.68           ( ( r1_tarski @ A @ B ) =>
% 1.46/1.68             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 1.46/1.68               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 1.46/1.68  thf('6', plain,
% 1.46/1.68      (![X38 : $i, X39 : $i]:
% 1.46/1.68         (~ (v1_relat_1 @ X38)
% 1.46/1.68          | (r1_tarski @ (k1_relat_1 @ X39) @ (k1_relat_1 @ X38))
% 1.46/1.68          | ~ (r1_tarski @ X39 @ X38)
% 1.46/1.68          | ~ (v1_relat_1 @ X39))),
% 1.46/1.68      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.46/1.68  thf('7', plain,
% 1.46/1.68      ((~ (v1_relat_1 @ sk_A)
% 1.46/1.68        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))
% 1.46/1.68        | ~ (v1_relat_1 @ sk_B))),
% 1.46/1.68      inference('sup-', [status(thm)], ['5', '6'])).
% 1.46/1.68  thf('8', plain, ((v1_relat_1 @ sk_A)),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('10', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k1_relat_1 @ sk_B))),
% 1.46/1.68      inference('demod', [status(thm)], ['7', '8', '9'])).
% 1.46/1.68  thf(t1_xboole_1, axiom,
% 1.46/1.68    (![A:$i,B:$i,C:$i]:
% 1.46/1.68     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 1.46/1.68       ( r1_tarski @ A @ C ) ))).
% 1.46/1.68  thf('11', plain,
% 1.46/1.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.46/1.68         (~ (r1_tarski @ X15 @ X16)
% 1.46/1.68          | ~ (r1_tarski @ X16 @ X17)
% 1.46/1.68          | (r1_tarski @ X15 @ X17))),
% 1.46/1.68      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.46/1.68  thf('12', plain,
% 1.46/1.68      (![X0 : $i]:
% 1.46/1.68         ((r1_tarski @ (k1_relat_1 @ sk_A) @ X0)
% 1.46/1.68          | ~ (r1_tarski @ (k1_relat_1 @ sk_B) @ X0))),
% 1.46/1.68      inference('sup-', [status(thm)], ['10', '11'])).
% 1.46/1.68  thf('13', plain,
% 1.46/1.68      ((~ (v1_relat_1 @ sk_B)
% 1.46/1.68        | (r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.46/1.68      inference('sup-', [status(thm)], ['4', '12'])).
% 1.46/1.68  thf('14', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('15', plain, ((r1_tarski @ (k1_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.46/1.68      inference('demod', [status(thm)], ['13', '14'])).
% 1.46/1.68  thf('16', plain,
% 1.46/1.68      (![X37 : $i]:
% 1.46/1.68         (((k3_relat_1 @ X37)
% 1.46/1.68            = (k2_xboole_0 @ (k1_relat_1 @ X37) @ (k2_relat_1 @ X37)))
% 1.46/1.68          | ~ (v1_relat_1 @ X37))),
% 1.46/1.68      inference('cnf', [status(esa)], [d6_relat_1])).
% 1.46/1.68  thf(commutativity_k2_tarski, axiom,
% 1.46/1.68    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.46/1.68  thf('17', plain,
% 1.46/1.68      (![X28 : $i, X29 : $i]:
% 1.46/1.68         ((k2_tarski @ X29 @ X28) = (k2_tarski @ X28 @ X29))),
% 1.46/1.68      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.46/1.68  thf(l51_zfmisc_1, axiom,
% 1.46/1.68    (![A:$i,B:$i]:
% 1.46/1.68     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.46/1.68  thf('18', plain,
% 1.46/1.68      (![X30 : $i, X31 : $i]:
% 1.46/1.68         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 1.46/1.68      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.46/1.68  thf('19', plain,
% 1.46/1.68      (![X0 : $i, X1 : $i]:
% 1.46/1.68         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.46/1.68      inference('sup+', [status(thm)], ['17', '18'])).
% 1.46/1.68  thf('20', plain,
% 1.46/1.68      (![X30 : $i, X31 : $i]:
% 1.46/1.68         ((k3_tarski @ (k2_tarski @ X30 @ X31)) = (k2_xboole_0 @ X30 @ X31))),
% 1.46/1.68      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.46/1.68  thf('21', plain,
% 1.46/1.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.46/1.68      inference('sup+', [status(thm)], ['19', '20'])).
% 1.46/1.68  thf('22', plain,
% 1.46/1.68      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 1.46/1.68      inference('cnf', [status(esa)], [t7_xboole_1])).
% 1.46/1.68  thf('23', plain,
% 1.46/1.68      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 1.46/1.68      inference('sup+', [status(thm)], ['21', '22'])).
% 1.46/1.68  thf('24', plain,
% 1.46/1.68      (![X0 : $i]:
% 1.46/1.68         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 1.46/1.68          | ~ (v1_relat_1 @ X0))),
% 1.46/1.68      inference('sup+', [status(thm)], ['16', '23'])).
% 1.46/1.68  thf('25', plain, ((r1_tarski @ sk_A @ sk_B)),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('26', plain,
% 1.46/1.68      (![X38 : $i, X39 : $i]:
% 1.46/1.68         (~ (v1_relat_1 @ X38)
% 1.46/1.68          | (r1_tarski @ (k2_relat_1 @ X39) @ (k2_relat_1 @ X38))
% 1.46/1.68          | ~ (r1_tarski @ X39 @ X38)
% 1.46/1.68          | ~ (v1_relat_1 @ X39))),
% 1.46/1.68      inference('cnf', [status(esa)], [t25_relat_1])).
% 1.46/1.68  thf('27', plain,
% 1.46/1.68      ((~ (v1_relat_1 @ sk_A)
% 1.46/1.68        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))
% 1.46/1.68        | ~ (v1_relat_1 @ sk_B))),
% 1.46/1.68      inference('sup-', [status(thm)], ['25', '26'])).
% 1.46/1.68  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('30', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B))),
% 1.46/1.68      inference('demod', [status(thm)], ['27', '28', '29'])).
% 1.46/1.68  thf('31', plain,
% 1.46/1.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.46/1.68         (~ (r1_tarski @ X15 @ X16)
% 1.46/1.68          | ~ (r1_tarski @ X16 @ X17)
% 1.46/1.68          | (r1_tarski @ X15 @ X17))),
% 1.46/1.68      inference('cnf', [status(esa)], [t1_xboole_1])).
% 1.46/1.68  thf('32', plain,
% 1.46/1.68      (![X0 : $i]:
% 1.46/1.68         ((r1_tarski @ (k2_relat_1 @ sk_A) @ X0)
% 1.46/1.68          | ~ (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 1.46/1.68      inference('sup-', [status(thm)], ['30', '31'])).
% 1.46/1.68  thf('33', plain,
% 1.46/1.68      ((~ (v1_relat_1 @ sk_B)
% 1.46/1.68        | (r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 1.46/1.68      inference('sup-', [status(thm)], ['24', '32'])).
% 1.46/1.68  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('35', plain, ((r1_tarski @ (k2_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.46/1.68      inference('demod', [status(thm)], ['33', '34'])).
% 1.46/1.68  thf(t8_xboole_1, axiom,
% 1.46/1.68    (![A:$i,B:$i,C:$i]:
% 1.46/1.68     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.46/1.68       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.46/1.68  thf('36', plain,
% 1.46/1.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.46/1.68         (~ (r1_tarski @ X25 @ X26)
% 1.46/1.68          | ~ (r1_tarski @ X27 @ X26)
% 1.46/1.68          | (r1_tarski @ (k2_xboole_0 @ X25 @ X27) @ X26))),
% 1.46/1.68      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.46/1.68  thf('37', plain,
% 1.46/1.68      (![X0 : $i]:
% 1.46/1.68         ((r1_tarski @ (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ X0) @ 
% 1.46/1.68           (k3_relat_1 @ sk_B))
% 1.46/1.68          | ~ (r1_tarski @ X0 @ (k3_relat_1 @ sk_B)))),
% 1.46/1.68      inference('sup-', [status(thm)], ['35', '36'])).
% 1.46/1.68  thf('38', plain,
% 1.46/1.68      ((r1_tarski @ 
% 1.46/1.68        (k2_xboole_0 @ (k2_relat_1 @ sk_A) @ (k1_relat_1 @ sk_A)) @ 
% 1.46/1.68        (k3_relat_1 @ sk_B))),
% 1.46/1.68      inference('sup-', [status(thm)], ['15', '37'])).
% 1.46/1.68  thf('39', plain,
% 1.46/1.68      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.46/1.68      inference('sup+', [status(thm)], ['19', '20'])).
% 1.46/1.68  thf('40', plain,
% 1.46/1.68      ((r1_tarski @ 
% 1.46/1.68        (k2_xboole_0 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)) @ 
% 1.46/1.68        (k3_relat_1 @ sk_B))),
% 1.46/1.68      inference('demod', [status(thm)], ['38', '39'])).
% 1.46/1.68  thf('41', plain,
% 1.46/1.68      (((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))
% 1.46/1.68        | ~ (v1_relat_1 @ sk_A))),
% 1.46/1.68      inference('sup+', [status(thm)], ['1', '40'])).
% 1.46/1.68  thf('42', plain, ((v1_relat_1 @ sk_A)),
% 1.46/1.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.46/1.68  thf('43', plain, ((r1_tarski @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B))),
% 1.46/1.68      inference('demod', [status(thm)], ['41', '42'])).
% 1.46/1.68  thf('44', plain, ($false), inference('demod', [status(thm)], ['0', '43'])).
% 1.46/1.68  
% 1.46/1.68  % SZS output end Refutation
% 1.46/1.68  
% 1.46/1.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
