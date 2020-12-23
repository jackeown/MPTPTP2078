%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YViPqzyK1z

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:01 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   59 (  72 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  393 ( 481 expanded)
%              Number of equality atoms :   41 (  52 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t80_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) )
        = A ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( ( k5_relat_1 @ X12 @ ( k6_relat_1 @ ( k2_relat_1 @ X12 ) ) )
        = X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t80_relat_1])).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ X0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('5',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('6',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5','6'])).

thf(t162_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_1])).

thf('8',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ X11 )
      | ( ( k5_relat_1 @ X10 @ ( k6_relat_1 @ X11 ) )
        = X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_B ) @ ( k6_relat_1 @ sk_A ) )
    = ( k6_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k7_relat_1 @ X14 @ X13 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X13 ) @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf('18',plain,
    ( ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,
    ( ( k7_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = ( k6_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(t201_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( ( k7_relat_1 @ B @ A )
              = ( k7_relat_1 @ C @ A ) )
           => ( ( k9_relat_1 @ B @ A )
              = ( k9_relat_1 @ C @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( ( k9_relat_1 @ X7 @ X6 )
        = ( k9_relat_1 @ X5 @ X6 ) )
      | ( ( k7_relat_1 @ X7 @ X6 )
       != ( k7_relat_1 @ X5 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t201_relat_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ sk_B )
       != ( k7_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_A ) )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ sk_B )
       != ( k7_relat_1 @ X0 @ sk_B ) )
      | ( ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
        = ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = ( k9_relat_1 @ ( k6_relat_1 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('27',plain,(
    ! [X8: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X8 ) )
      = X8 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i] :
      ( ( ( k9_relat_1 @ X4 @ ( k1_relat_1 @ X4 ) )
        = ( k2_relat_1 @ X4 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
        = ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,(
    ! [X3: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( ( k6_relat_1 @ sk_B )
     != ( k6_relat_1 @ sk_B ) )
    | ( ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
      = sk_B ) ),
    inference(demod,[status(thm)],['25','26','32'])).

thf('34',plain,
    ( ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
    = sk_B ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ( k9_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.YViPqzyK1z
% 0.13/0.37  % Computer   : n001.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 20:48:30 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.46  % Solved by: fo/fo7.sh
% 0.23/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.46  % done 22 iterations in 0.014s
% 0.23/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.46  % SZS output start Refutation
% 0.23/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.46  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.23/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.23/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.23/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.46  thf(t80_relat_1, axiom,
% 0.23/0.46    (![A:$i]:
% 0.23/0.46     ( ( v1_relat_1 @ A ) =>
% 0.23/0.46       ( ( k5_relat_1 @ A @ ( k6_relat_1 @ ( k2_relat_1 @ A ) ) ) = ( A ) ) ))).
% 0.23/0.46  thf('0', plain,
% 0.23/0.46      (![X12 : $i]:
% 0.23/0.46         (((k5_relat_1 @ X12 @ (k6_relat_1 @ (k2_relat_1 @ X12))) = (X12))
% 0.23/0.46          | ~ (v1_relat_1 @ X12))),
% 0.23/0.46      inference('cnf', [status(esa)], [t80_relat_1])).
% 0.23/0.46  thf(t94_relat_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( v1_relat_1 @ B ) =>
% 0.23/0.46       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.23/0.46  thf('1', plain,
% 0.23/0.46      (![X13 : $i, X14 : $i]:
% 0.23/0.46         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_relat_1 @ X13) @ X14))
% 0.23/0.46          | ~ (v1_relat_1 @ X14))),
% 0.23/0.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.23/0.46  thf('2', plain,
% 0.23/0.46      (![X0 : $i]:
% 0.23/0.46         (((k7_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0))) @ X0)
% 0.23/0.46            = (k6_relat_1 @ X0))
% 0.23/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.23/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ (k2_relat_1 @ (k6_relat_1 @ X0)))))),
% 0.23/0.46      inference('sup+', [status(thm)], ['0', '1'])).
% 0.23/0.46  thf(t71_relat_1, axiom,
% 0.23/0.46    (![A:$i]:
% 0.23/0.46     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.23/0.46       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.23/0.46  thf('3', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.23/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.46  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.23/0.46  thf('4', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.23/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.23/0.46  thf('5', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.23/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.46  thf('6', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.23/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.23/0.46  thf('7', plain,
% 0.23/0.46      (![X0 : $i]: ((k7_relat_1 @ (k6_relat_1 @ X0) @ X0) = (k6_relat_1 @ X0))),
% 0.23/0.46      inference('demod', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.23/0.46  thf(t162_funct_1, conjecture,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.46       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.23/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.46    (~( ![A:$i,B:$i]:
% 0.23/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.23/0.46          ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) )),
% 0.23/0.46    inference('cnf.neg', [status(esa)], [t162_funct_1])).
% 0.23/0.46  thf('8', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf(t3_subset, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.23/0.46  thf('9', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.23/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.23/0.46  thf('10', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.23/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.23/0.46  thf('11', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.23/0.46      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.46  thf(t79_relat_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( v1_relat_1 @ B ) =>
% 0.23/0.46       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.23/0.46         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.23/0.46  thf('12', plain,
% 0.23/0.46      (![X10 : $i, X11 : $i]:
% 0.23/0.46         (~ (r1_tarski @ (k2_relat_1 @ X10) @ X11)
% 0.23/0.46          | ((k5_relat_1 @ X10 @ (k6_relat_1 @ X11)) = (X10))
% 0.23/0.46          | ~ (v1_relat_1 @ X10))),
% 0.23/0.46      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.23/0.46  thf('13', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.23/0.46          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.23/0.46          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.23/0.46              = (k6_relat_1 @ X0)))),
% 0.23/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.46  thf('14', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.23/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.23/0.46  thf('15', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         (~ (r1_tarski @ X0 @ X1)
% 0.23/0.46          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.23/0.46              = (k6_relat_1 @ X0)))),
% 0.23/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.23/0.46  thf('16', plain,
% 0.23/0.46      (((k5_relat_1 @ (k6_relat_1 @ sk_B) @ (k6_relat_1 @ sk_A))
% 0.23/0.46         = (k6_relat_1 @ sk_B))),
% 0.23/0.46      inference('sup-', [status(thm)], ['10', '15'])).
% 0.23/0.46  thf('17', plain,
% 0.23/0.46      (![X13 : $i, X14 : $i]:
% 0.23/0.46         (((k7_relat_1 @ X14 @ X13) = (k5_relat_1 @ (k6_relat_1 @ X13) @ X14))
% 0.23/0.46          | ~ (v1_relat_1 @ X14))),
% 0.23/0.46      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.23/0.46  thf('18', plain,
% 0.23/0.46      ((((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_B))
% 0.23/0.46        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A)))),
% 0.23/0.46      inference('sup+', [status(thm)], ['16', '17'])).
% 0.23/0.46  thf('19', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.23/0.46      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.23/0.46  thf('20', plain,
% 0.23/0.46      (((k7_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (k6_relat_1 @ sk_B))),
% 0.23/0.46      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.46  thf(t201_relat_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( v1_relat_1 @ B ) =>
% 0.23/0.46       ( ![C:$i]:
% 0.23/0.46         ( ( v1_relat_1 @ C ) =>
% 0.23/0.46           ( ( ( k7_relat_1 @ B @ A ) = ( k7_relat_1 @ C @ A ) ) =>
% 0.23/0.46             ( ( k9_relat_1 @ B @ A ) = ( k9_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.23/0.46  thf('21', plain,
% 0.23/0.46      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ X5)
% 0.23/0.46          | ((k9_relat_1 @ X7 @ X6) = (k9_relat_1 @ X5 @ X6))
% 0.23/0.46          | ((k7_relat_1 @ X7 @ X6) != (k7_relat_1 @ X5 @ X6))
% 0.23/0.46          | ~ (v1_relat_1 @ X7))),
% 0.23/0.47      inference('cnf', [status(esa)], [t201_relat_1])).
% 0.23/0.47  thf('22', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (((k6_relat_1 @ sk_B) != (k7_relat_1 @ X0 @ sk_B))
% 0.23/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ sk_A))
% 0.23/0.47          | ((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.23/0.47              = (k9_relat_1 @ X0 @ sk_B))
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.47  thf('23', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.23/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.23/0.47  thf('24', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (((k6_relat_1 @ sk_B) != (k7_relat_1 @ X0 @ sk_B))
% 0.23/0.47          | ((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.23/0.47              = (k9_relat_1 @ X0 @ sk_B))
% 0.23/0.47          | ~ (v1_relat_1 @ X0))),
% 0.23/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.23/0.47  thf('25', plain,
% 0.23/0.47      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.23/0.47        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_B))
% 0.23/0.47        | ((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B)
% 0.23/0.47            = (k9_relat_1 @ (k6_relat_1 @ sk_B) @ sk_B)))),
% 0.23/0.47      inference('sup-', [status(thm)], ['7', '24'])).
% 0.23/0.47  thf('26', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.23/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.23/0.47  thf('27', plain, (![X8 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X8)) = (X8))),
% 0.23/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.47  thf(t146_relat_1, axiom,
% 0.23/0.47    (![A:$i]:
% 0.23/0.47     ( ( v1_relat_1 @ A ) =>
% 0.23/0.47       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.23/0.47  thf('28', plain,
% 0.23/0.47      (![X4 : $i]:
% 0.23/0.47         (((k9_relat_1 @ X4 @ (k1_relat_1 @ X4)) = (k2_relat_1 @ X4))
% 0.23/0.47          | ~ (v1_relat_1 @ X4))),
% 0.23/0.47      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.23/0.47  thf('29', plain,
% 0.23/0.47      (![X0 : $i]:
% 0.23/0.47         (((k9_relat_1 @ (k6_relat_1 @ X0) @ X0)
% 0.23/0.47            = (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.23/0.47          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.23/0.47      inference('sup+', [status(thm)], ['27', '28'])).
% 0.23/0.47  thf('30', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 0.23/0.47      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.23/0.47  thf('31', plain, (![X3 : $i]: (v1_relat_1 @ (k6_relat_1 @ X3))),
% 0.23/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.23/0.47  thf('32', plain,
% 0.23/0.47      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.23/0.47      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.23/0.47  thf('33', plain,
% 0.23/0.47      ((((k6_relat_1 @ sk_B) != (k6_relat_1 @ sk_B))
% 0.23/0.47        | ((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B)))),
% 0.23/0.47      inference('demod', [status(thm)], ['25', '26', '32'])).
% 0.23/0.47  thf('34', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) = (sk_B))),
% 0.23/0.47      inference('simplify', [status(thm)], ['33'])).
% 0.23/0.47  thf('35', plain, (((k9_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B) != (sk_B))),
% 0.23/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.47  thf('36', plain, ($false),
% 0.23/0.47      inference('simplify_reflect-', [status(thm)], ['34', '35'])).
% 0.23/0.47  
% 0.23/0.47  % SZS output end Refutation
% 0.23/0.47  
% 0.23/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
