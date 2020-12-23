%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8TtWWphIod

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:34 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  68 expanded)
%              Number of leaves         :   24 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  315 ( 395 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X42: $i,X43: $i] :
      ( ( X43
       != ( k1_wellord2 @ X42 ) )
      | ( ( k3_relat_1 @ X43 )
        = X42 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X42: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X42 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X42 ) )
        = X42 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X42: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X42 ) )
      = X42 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d6_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k3_relat_1 @ A )
        = ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X38: $i] :
      ( ( ( k3_relat_1 @ X38 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_tarski @ X5 @ X4 )
      = ( k2_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X33 @ X34 ) )
      = ( k2_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','13'])).

thf('15',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X42: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X42 ) )
      = X42 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('18',plain,(
    ! [X38: $i] :
      ( ( ( k3_relat_1 @ X38 )
        = ( k2_xboole_0 @ ( k1_relat_1 @ X38 ) @ ( k2_relat_1 @ X38 ) ) )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d6_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X0 ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('23',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('24',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X39 ) @ X40 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X39 ) @ X41 )
      | ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ( m1_subset_1 @ ( k1_wellord2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X46: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_wellord2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k1_wellord2 @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_wellord2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X35: $i,X36: $i] :
      ( ( r1_tarski @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8TtWWphIod
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:45:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 77 iterations in 0.036s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.20/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.49  thf(t33_wellord2, conjecture,
% 0.20/0.49    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(d1_wellord2, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.20/0.49         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.49           ( ![C:$i,D:$i]:
% 0.20/0.49             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.20/0.49               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.20/0.49                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X42 : $i, X43 : $i]:
% 0.20/0.49         (((X43) != (k1_wellord2 @ X42))
% 0.20/0.49          | ((k3_relat_1 @ X43) = (X42))
% 0.20/0.49          | ~ (v1_relat_1 @ X43))),
% 0.20/0.49      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X42 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X42))
% 0.20/0.49          | ((k3_relat_1 @ (k1_wellord2 @ X42)) = (X42)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.49  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.20/0.49  thf('3', plain, (![X46 : $i]: (v1_relat_1 @ (k1_wellord2 @ X46))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('4', plain, (![X42 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X42)) = (X42))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf(d6_relat_1, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ A ) =>
% 0.20/0.49       ( ( k3_relat_1 @ A ) =
% 0.20/0.49         ( k2_xboole_0 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X38 : $i]:
% 0.20/0.49         (((k3_relat_1 @ X38)
% 0.20/0.49            = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 0.20/0.49          | ~ (v1_relat_1 @ X38))),
% 0.20/0.49      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.20/0.49  thf(commutativity_k2_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i]: ((k2_tarski @ X5 @ X4) = (k2_tarski @ X4 @ X5))),
% 0.20/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.49  thf(l51_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X33 : $i, X34 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 0.20/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X33 : $i, X34 : $i]:
% 0.20/0.49         ((k3_tarski @ (k2_tarski @ X33 @ X34)) = (k2_xboole_0 @ X33 @ X34))),
% 0.20/0.49      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf(t7_xboole_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k2_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['5', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['4', '13'])).
% 0.20/0.49  thf('15', plain, (![X46 : $i]: (v1_relat_1 @ (k1_wellord2 @ X46))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.20/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.49  thf('17', plain, (![X42 : $i]: ((k3_relat_1 @ (k1_wellord2 @ X42)) = (X42))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X38 : $i]:
% 0.20/0.49         (((k3_relat_1 @ X38)
% 0.20/0.49            = (k2_xboole_0 @ (k1_relat_1 @ X38) @ (k2_relat_1 @ X38)))
% 0.20/0.49          | ~ (v1_relat_1 @ X38))),
% 0.20/0.49      inference('cnf', [status(esa)], [d6_relat_1])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_relat_1 @ X0) @ (k3_relat_1 @ X0))
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['17', '20'])).
% 0.20/0.49  thf('22', plain, (![X46 : $i]: (v1_relat_1 @ (k1_wellord2 @ X46))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k1_wellord2 @ X0)) @ X0)),
% 0.20/0.49      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf(t11_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.20/0.49           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.20/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.20/0.49  thf('24', plain,
% 0.20/0.49      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.20/0.49         (~ (r1_tarski @ (k1_relat_1 @ X39) @ X40)
% 0.20/0.49          | ~ (r1_tarski @ (k2_relat_1 @ X39) @ X41)
% 0.20/0.49          | (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.20/0.49          | ~ (v1_relat_1 @ X39))),
% 0.20/0.49      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X0))
% 0.20/0.49          | (m1_subset_1 @ (k1_wellord2 @ X0) @ 
% 0.20/0.49             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.20/0.49          | ~ (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.49  thf('26', plain, (![X46 : $i]: (v1_relat_1 @ (k1_wellord2 @ X46))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((m1_subset_1 @ (k1_wellord2 @ X0) @ 
% 0.20/0.49           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.20/0.49          | ~ (r1_tarski @ (k2_relat_1 @ (k1_wellord2 @ X0)) @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (m1_subset_1 @ (k1_wellord2 @ X0) @ 
% 0.20/0.49          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['16', '27'])).
% 0.20/0.49  thf(t3_subset, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (![X35 : $i, X36 : $i]:
% 0.20/0.49         ((r1_tarski @ X35 @ X36) | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.49  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
