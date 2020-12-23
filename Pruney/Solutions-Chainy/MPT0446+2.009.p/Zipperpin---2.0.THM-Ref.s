%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.clAQhVBNxD

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:52 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   66 (  86 expanded)
%              Number of leaves         :   25 (  35 expanded)
%              Depth                    :   11
%              Number of atoms          :  354 ( 635 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
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
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X46 @ X47 ) @ X48 )
      | ( r2_hidden @ X46 @ ( k1_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
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
    ! [X45: $i] :
      ( ( ( k3_relat_1 @ X45 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X45 ) @ ( k2_relat_1 @ X45 ) ) )
      | ~ ( v1_relat_1 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('17',plain,(
    r2_hidden @ ( k4_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X46 @ X47 ) @ X48 )
      | ( r2_hidden @ X47 @ ( k2_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
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

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('23',plain,(
    ! [X35: $i] :
      ( r1_tarski @ X35 @ ( k1_zfmisc_1 @ ( k3_tarski @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ X38 @ X37 )
      | ~ ( r1_tarski @ ( k2_tarski @ X36 @ X38 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X43: $i,X44: $i] :
      ( ( m1_subset_1 @ X43 @ X44 )
      | ~ ( r2_hidden @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('29',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X40 @ X41 )
      | ( r2_hidden @ X40 @ X42 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

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
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.clAQhVBNxD
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 14:33:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.36/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.56  % Solved by: fo/fo7.sh
% 0.36/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.56  % done 153 iterations in 0.093s
% 0.36/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.56  % SZS output start Refutation
% 0.36/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.36/0.56  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.36/0.56  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.36/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.56  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.56  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.56  thf(t30_relat_1, conjecture,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( v1_relat_1 @ C ) =>
% 0.36/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.36/0.56         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.36/0.56           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.36/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.56        ( ( v1_relat_1 @ C ) =>
% 0.36/0.56          ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.36/0.56            ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.36/0.56              ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )),
% 0.36/0.56    inference('cnf.neg', [status(esa)], [t30_relat_1])).
% 0.36/0.56  thf('0', plain,
% 0.36/0.56      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))
% 0.36/0.56        | ~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('1', plain,
% 0.36/0.56      ((~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)))
% 0.36/0.56         <= (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf(d6_relat_1, axiom,
% 0.36/0.56    (![A:$i]:
% 0.36/0.56     ( ( v1_relat_1 @ A ) =>
% 0.36/0.56       ( ( k3_relat_1 @ A ) =
% 0.36/0.56         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.36/0.56  thf('2', plain,
% 0.36/0.56      (![X45 : $i]:
% 0.36/0.56         (((k3_relat_1 @ X45)
% 0.36/0.56            = (k2_xboole_0 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45)))
% 0.36/0.56          | ~ (v1_relat_1 @ X45))),
% 0.36/0.56      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.36/0.56  thf('3', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf(t20_relat_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( v1_relat_1 @ C ) =>
% 0.36/0.56       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.36/0.56         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.36/0.56           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.36/0.56  thf('4', plain,
% 0.36/0.56      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.36/0.56         (~ (r2_hidden @ (k4_tarski @ X46 @ X47) @ X48)
% 0.36/0.56          | (r2_hidden @ X46 @ (k1_relat_1 @ X48))
% 0.36/0.56          | ~ (v1_relat_1 @ X48))),
% 0.36/0.56      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.36/0.56  thf('5', plain,
% 0.36/0.56      ((~ (v1_relat_1 @ sk_C_1) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.36/0.56  thf('6', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('7', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.36/0.56      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.56  thf(t7_xboole_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.56  thf('8', plain,
% 0.36/0.56      (![X4 : $i, X5 : $i]: (r1_tarski @ X4 @ (k2_xboole_0 @ X4 @ X5))),
% 0.36/0.56      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.36/0.56  thf(d3_tarski, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.36/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.36/0.56  thf('9', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X0 @ X1)
% 0.36/0.56          | (r2_hidden @ X0 @ X2)
% 0.36/0.56          | ~ (r1_tarski @ X1 @ X2))),
% 0.36/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.36/0.56  thf('10', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.36/0.56      inference('sup-', [status(thm)], ['8', '9'])).
% 0.36/0.56  thf('11', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (r2_hidden @ sk_A @ (k2_xboole_0 @ (k1_relat_1 @ sk_C_1) @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['7', '10'])).
% 0.36/0.56  thf('12', plain,
% 0.36/0.56      (((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.36/0.56      inference('sup+', [status(thm)], ['2', '11'])).
% 0.36/0.56  thf('13', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('14', plain, ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))),
% 0.36/0.56      inference('demod', [status(thm)], ['12', '13'])).
% 0.36/0.56  thf('15', plain,
% 0.36/0.56      (($false) <= (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))))),
% 0.36/0.56      inference('demod', [status(thm)], ['1', '14'])).
% 0.36/0.56  thf('16', plain,
% 0.36/0.56      (![X45 : $i]:
% 0.36/0.56         (((k3_relat_1 @ X45)
% 0.36/0.56            = (k2_xboole_0 @ (k1_relat_1 @ X45) @ (k2_relat_1 @ X45)))
% 0.36/0.56          | ~ (v1_relat_1 @ X45))),
% 0.36/0.56      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.36/0.56  thf('17', plain, ((r2_hidden @ (k4_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('18', plain,
% 0.36/0.56      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.36/0.56         (~ (r2_hidden @ (k4_tarski @ X46 @ X47) @ X48)
% 0.36/0.56          | (r2_hidden @ X47 @ (k2_relat_1 @ X48))
% 0.36/0.56          | ~ (v1_relat_1 @ X48))),
% 0.36/0.56      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.36/0.56  thf('19', plain,
% 0.36/0.56      ((~ (v1_relat_1 @ sk_C_1) | (r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.36/0.56  thf('20', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('21', plain, ((r2_hidden @ sk_B @ (k2_relat_1 @ sk_C_1))),
% 0.36/0.56      inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.56  thf(l51_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.36/0.56  thf('22', plain,
% 0.36/0.56      (![X33 : $i, X34 : $i]:
% 0.36/0.56         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 0.36/0.56      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.36/0.56  thf(t100_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.36/0.56  thf('23', plain,
% 0.36/0.56      (![X35 : $i]: (r1_tarski @ X35 @ (k1_zfmisc_1 @ (k3_tarski @ X35)))),
% 0.36/0.56      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.36/0.56  thf('24', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (r1_tarski @ (k2_tarski @ X1 @ X0) @ 
% 0.36/0.56          (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.56      inference('sup+', [status(thm)], ['22', '23'])).
% 0.36/0.56  thf(t38_zfmisc_1, axiom,
% 0.36/0.56    (![A:$i,B:$i,C:$i]:
% 0.36/0.56     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.36/0.56       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.36/0.56  thf('25', plain,
% 0.36/0.56      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.36/0.56         ((r2_hidden @ X38 @ X37)
% 0.36/0.56          | ~ (r1_tarski @ (k2_tarski @ X36 @ X38) @ X37))),
% 0.36/0.56      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.36/0.56  thf('26', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (r2_hidden @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.36/0.56  thf(t1_subset, axiom,
% 0.36/0.56    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.36/0.56  thf('27', plain,
% 0.36/0.56      (![X43 : $i, X44 : $i]:
% 0.36/0.56         ((m1_subset_1 @ X43 @ X44) | ~ (r2_hidden @ X43 @ X44))),
% 0.36/0.56      inference('cnf', [status(esa)], [t1_subset])).
% 0.36/0.56  thf('28', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i]:
% 0.36/0.56         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.56  thf(l3_subset_1, axiom,
% 0.36/0.56    (![A:$i,B:$i]:
% 0.36/0.56     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.36/0.56  thf('29', plain,
% 0.36/0.56      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.36/0.56         (~ (r2_hidden @ X40 @ X41)
% 0.36/0.56          | (r2_hidden @ X40 @ X42)
% 0.36/0.56          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42)))),
% 0.36/0.56      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.36/0.56  thf('30', plain,
% 0.36/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.56         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X0))),
% 0.36/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.36/0.56  thf('31', plain,
% 0.36/0.56      (![X0 : $i]:
% 0.36/0.56         (r2_hidden @ sk_B @ (k2_xboole_0 @ X0 @ (k2_relat_1 @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['21', '30'])).
% 0.36/0.56  thf('32', plain,
% 0.36/0.56      (((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)) | ~ (v1_relat_1 @ sk_C_1))),
% 0.36/0.56      inference('sup+', [status(thm)], ['16', '31'])).
% 0.36/0.56  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.56  thf('34', plain, ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))),
% 0.36/0.56      inference('demod', [status(thm)], ['32', '33'])).
% 0.36/0.56  thf('35', plain,
% 0.36/0.56      ((~ (r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))
% 0.36/0.56         <= (~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1))))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('36', plain, (((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))),
% 0.36/0.56      inference('sup-', [status(thm)], ['34', '35'])).
% 0.36/0.56  thf('37', plain,
% 0.36/0.56      (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1))) | 
% 0.36/0.56       ~ ((r2_hidden @ sk_B @ (k3_relat_1 @ sk_C_1)))),
% 0.36/0.56      inference('split', [status(esa)], ['0'])).
% 0.36/0.56  thf('38', plain, (~ ((r2_hidden @ sk_A @ (k3_relat_1 @ sk_C_1)))),
% 0.36/0.56      inference('sat_resolution*', [status(thm)], ['36', '37'])).
% 0.36/0.56  thf('39', plain, ($false),
% 0.36/0.56      inference('simpl_trail', [status(thm)], ['15', '38'])).
% 0.36/0.56  
% 0.36/0.56  % SZS output end Refutation
% 0.36/0.56  
% 0.36/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
